mutable struct SaturationReport
  reason::Union{Symbol,Nothing}
  egraph::EGraph
  iterations::Int
  to::TimerOutput
end

SaturationReport() = SaturationReport(nothing, EGraph(), 0, TimerOutput())
SaturationReport(g::EGraph) = SaturationReport(nothing, g, 0, TimerOutput())



# string representation of timedata
function Base.show(io::IO, x::SaturationReport)
  g = x.egraph
  println(io, "SaturationReport")
  println(io, "=================")
  println(io, "\tStop Reason: $(x.reason)")
  println(io, "\tIterations: $(x.iterations)")
  println(io, "\tEGraph Size: $(length(g.classes)) eclasses, $(length(g.memo)) nodes")
  print_timer(io, x.to)
end

"""
Configurable Parameters for the equality saturation process.
"""
Base.@kwdef mutable struct SaturationParams
  timeout::Int = 8
  "Timeout in nanoseconds"
  timelimit::UInt64 = 0
  "Maximum number of eclasses allowed"
  eclasslimit::Int = 5000
  enodelimit::Int = 15000
  goal::Function = (g::EGraph) -> false
  scheduler::Type{<:AbstractScheduler} = BackoffScheduler
  schedulerparams::NamedTuple = (;)
  threaded::Bool = false
  timer::Bool = true
  "Activate check for memoization of nodes (hashcons) after rebuilding"
  check_memo::Bool = false
  "Activate check for join-semilattice invariant for semantic analysis values after rebuilding"
  check_analysis::Bool = false
end

function cached_ids(g::EGraph, p::PatExpr)::Vector{Id}
  if isground(p)
    id = lookup_pat(g, p)
    iszero(id) ? UNDEF_ID_VEC : [id] # TODO: vector allocation
  else
    get(g.classes_by_op, IdKey(v_signature(p.n)), UNDEF_ID_VEC)
  end
end

function cached_ids(g::EGraph, p::PatLiteral) # p is a literal
  id = lookup_pat(g, p)
  id > 0 && return [id] # TODO: vector allocation
  return UNDEF_ID_VEC
end

cached_ids(g::EGraph, p::PatVar) = Iterators.map(x -> x.val, keys(g.classes))

"""
Returns an iterator of `Match`es.
"""
function eqsat_search!(
  g::EGraph,
  theory::Theory,
  scheduler::AbstractScheduler,
  report::SaturationReport,
  ematch_buffer::OptBuffer{UInt128},
)::Int
  n_matches = 0

  g.needslock && lock(g.lock)
  empty!(ematch_buffer)
  g.needslock && unlock(g.lock)


  @debug "SEARCHING"
  for (rule_idx, rule) in enumerate(theory)
    prev_matches = n_matches
    @timeit report.to string(rule_idx) begin
      prev_matches = n_matches
      # don't apply banned rules
      if !cansearch(scheduler, rule_idx)
        @debug "$rule is banned"
        continue
      end
      ids_left = cached_ids(g, rule.left)

      for i in ids_left
        cansearch(scheduler, rule_idx, i, 1) || continue
        n_matches += rule.ematcher_left!(g, rule_idx, i, rule.stack, ematch_buffer)
        inform!(scheduler, rule_idx, i, n_matches)
      end

      if is_bidirectional(rule)
        ids_right = cached_ids(g, rule.right)
        for i in ids_right
          cansearch(scheduler, rule_idx, i, -1) || continue
          n_matches += rule.ematcher_right!(g, rule_idx, i, rule.stack, ematch_buffer)
          inform!(scheduler, rule_idx, i, n_matches)
        end
      end

      n_matches - prev_matches > 0 && @debug "Rule $rule_idx: $rule produced $(n_matches - prev_matches) matches"
      # if n_matches - prev_matches > 2 && rule_idx == 2
      #   @debug buffer_readable(g, old_len)
      # end
      inform!(scheduler, rule_idx, n_matches)
    end
  end


  return n_matches
end

instantiated_size(bindings, @nospecialize(g::EGraph), p::PatLiteral)::Int = 1
instantiated_size(bindings, @nospecialize(g::EGraph), p::PatVar)::Int = g[v_pair_first(bindings[p.idx])].data.len # TODO requires folding analysis
instantiated_size(bindings, g::EGraph{Expr}, p::PatExpr)::Int = 1 + sum(chld -> instantiated_size(bindings, g, chld), p.children)

function instantiate_enode!(bindings, @nospecialize(g::EGraph), p::PatLiteral)::Id
  add_constant_hashed!(g, p.value, v_head(p.n))
  g.debuglog && println(g.log, "instantiated literal bindings $bindings $p (constant value: $(p.value) hash: $(v_head(p.n)))")
  add!(g, p.n, true)
end

instantiate_enode!(bindings, @nospecialize(g::EGraph), p::PatVar)::Id = v_pair_first(bindings[p.idx])
function instantiate_enode!(bindings, g::EGraph{ExpressionType}, p::PatExpr)::Id where {ExpressionType}
  add_constant_hashed!(g, p.head, p.head_hash)

  for i in v_children_range(p.n)
    @inbounds p.n[i] = instantiate_enode!(bindings, g, p.children[i - VECEXPR_META_LENGTH])
  end
  add!(g, p.n, true)
end

function instantiate_enode!(bindings, g::EGraph{Expr}, p::PatExpr)::Id
  add_constant_hashed!(g, p.quoted_head, p.quoted_head_hash)
  v_set_head!(p.n, p.quoted_head_hash)

  for i in v_children_range(p.n)
    @inbounds p.n[i] = instantiate_enode!(bindings, g, p.children[i - VECEXPR_META_LENGTH])
  end
  g.debuglog && println(g.log, "instantiated expr bindings $bindings $p (constant value: $(p.quoted_head) hash: $(p.quoted_head_hash) $(map(Int, v_children(p.n)))")
  add!(g, p.n, true)
end

"""
Instantiate argument for dynamic rule application in e-graph
"""
function instantiate_actual_param!(bindings, g::EGraph, i)
  ecid = v_pair_first(bindings[i])
  literal_position = reinterpret(Int, v_pair_last(bindings[i]))
  ecid <= 0 && error("unbound pattern variable")
  eclass = g[ecid]
  if literal_position > 0
    @assert !v_isexpr(eclass[literal_position])
    return get_constant(g, v_head(eclass[literal_position]))
  end
  return eclass
end


struct RuleApplicationResult
  halt_reason::Symbol
  l::Id
  r::Id
end

function apply_rule!(
  bindings::SubArray{UInt128,1,Vector{UInt128},Tuple{UnitRange{Int64}},true},
  g::EGraph,
  rule::RewriteRule,
  id::Id,
  direction::Int,
)::RuleApplicationResult
  if rule.op === (-->) # DirectedRule
    instantiated_size(bindings, g, rule.right) <= 20 || return RuleApplicationResult(:nothing, 0, 0)
    new_id::Id = instantiate_enode!(bindings, g, rule.right)
    RuleApplicationResult(:nothing, new_id, id)
  elseif rule.op === (==) # EqualityRule
    pat_to_inst = direction == 1 ? rule.right : rule.left
    instantiated_size(bindings, g, pat_to_inst) <= 20 || return RuleApplicationResult(:nothing, 0, 0)
    new_id = instantiate_enode!(bindings, g, pat_to_inst)
    RuleApplicationResult(:nothing, new_id, id)
  elseif rule.op === (!=) # UnequalRule
    pat_to_inst = direction == 1 ? rule.right : rule.left
    instantiated_size(bindings, g, pat_to_inst) <= 20 || return RuleApplicationResult(:nothing, 0, 0)
    other_id = instantiate_enode!(bindings, g, pat_to_inst)

    if find(g, id) == find(g, other_id)
      @debug "$rule produced a contradiction!"
      return RuleApplicationResult(:contradiction, 0, 0)
    end
    RuleApplicationResult(:nothing, 0, 0)
  elseif rule.op === (|>) # DynamicRule
    r = rule.right(id, g, (instantiate_actual_param!(bindings, g, i) for i in 1:length(rule.patvars))...)
    # TODO: size limit for dynamic expressions
    isnothing(r) && return RuleApplicationResult(:nothing, 0, 0)
    rcid = addexpr!(g, r)
    RuleApplicationResult(:nothing, rcid, id)
  else
    RuleApplicationResult(:error, 0, 0)
  end
end


"Useful for debugging: prints the content of the e-graph match buffer in readable format."
function buffer_readable(g, limit, ematch_buffer)
  k = length(ematch_buffer)

  while k > limit
    delimiter = ematch_buffer.v[k]
    @assert delimiter == 0xffffffffffffffffffffffffffffffff
    n = k - 1

    next_delimiter_idx = 0
    n_elems = 0
    for i in n:-1:1
      n_elems += 1
      if ematch_buffer.v[i] == 0xffffffffffffffffffffffffffffffff
        n_elems -= 1
        next_delimiter_idx = i
        break
      end
    end

    match_info = ematch_buffer.v[next_delimiter_idx + 1]
    id = v_pair_first(match_info)
    rule_idx = reinterpret(Int, v_pair_last(match_info))
    rule_idx = abs(rule_idx)

    bindings = @view ematch_buffer.v[(next_delimiter_idx + 2):n]

    print("$id rule_idx: $rule_idx E-Classes: ", map(x -> reinterpret(Int, v_pair_first(x)), bindings))
    print(" Nodes: ", map(x -> reinterpret(Int, v_pair_last(x)), bindings), "\n")

    k = next_delimiter_idx
  end
end

const CHECK_GOAL_EVERY_N_MATCHES = 20

function eqsat_apply!(
  g::EGraph,
  theory::Theory,
  rep::SaturationReport,
  params::SaturationParams,
  ematch_buffer::OptBuffer{UInt128},
)
  n_matches = 0
  k = length(ematch_buffer)

  # @debug "APPLYING $(count((==)(0xffffffffffffffffffffffffffffffff), ematch_buffer)) matches"
  g.needslock && lock(g.lock)
  while k > 0

    if n_matches % CHECK_GOAL_EVERY_N_MATCHES == 0 && params.goal(g)
      @debug "Goal reached"
      rep.reason = :goalreached
      return
    end

    delimiter = ematch_buffer.v[k]
    @assert delimiter == 0xffffffffffffffffffffffffffffffff
    n = k - 1

    next_delimiter_idx = 0
    n_elems = 0
    for i in n:-1:1
      n_elems += 1
      if ematch_buffer.v[i] == 0xffffffffffffffffffffffffffffffff
        n_elems -= 1
        next_delimiter_idx = i
        break
      end
    end

    n_matches += 1
    match_info = ematch_buffer.v[next_delimiter_idx + 1]
    id = v_pair_first(match_info)
    rule_idx = reinterpret(Int, v_pair_last(match_info))
    direction = sign(rule_idx)
    rule_idx = abs(rule_idx)
    rule = theory[rule_idx]

    bindings = @view ematch_buffer.v[(next_delimiter_idx + 2):n]


    g.debuglog && println(g.log, "id: $id")
    g.debuglog && println(g.log, "rule: $rule dir $direction")
    # r = rule.right(id, g, (instantiate_actual_param!(bindings, g, i) for i in 1:length(rule.patvars))...)
    # println(g.log, "$r")
    
    g.debuglog && println(g.log, "bindings: $(bindings)")
    g.debuglog && println(g.log, "patvars: $(rule.patvars)")

    res = apply_rule!(bindings, g, rule, id, direction)

    g.debuglog && println(g.log, "res $res")

    k = next_delimiter_idx
    if res.halt_reason !== :nothing
      rep.reason = res.halt_reason
      return
    end

    c1 = 0
    c2 = 0
    try
      if !iszero(res.l) && !iszero(res.r)
        c1 = g[res.l]
        c2 = g[res.r]

      end
      #println("num nodes before union! $(length(g.memo))")
      !iszero(res.l) && !iszero(res.r) && union!(g, res.l, res.r)
      #println("num nodes after union! $(length(g.memo))")
    catch ex
      # buffer_readable(g, k, ematch_buffer)
      # println(g)
      # println("Exception when merging $(res.l) $(map(n -> to_expr(g, n), c1.nodes)) \n and $(res.r) $(map(n -> to_expr(g, n), c2.nodes)) after applying rule $rule")
      println("Exception when merging $(res.l) (data: $(c1.data)) and $(res.r) (data: $(c2.data)) after applying rule $rule")
      println("bindings $bindings")
      println("$(rule.patvars)")
      # try
      #   r = rule.right(id, g, (instantiate_actual_param!(bindings, g, i) for i in 1:length(rule.patvars))...)
      #   println("expr: $r")
      # catch _
      # end
      rethrow()
    end
    
    if params.enodelimit > 0 && length(g.memo) > params.enodelimit
      @debug "Too many enodes"
      rep.reason = :enodelimit
      break
    end
  end
  if params.goal(g)
    @debug "Goal reached"
    rep.reason = :goalreached
    return
  end

  empty!(ematch_buffer)

  g.needslock && unlock(g.lock)
end


"""
Core algorithm of the library: the equality saturation step.
"""
function eqsat_step!(
  g::EGraph,
  theory::Theory,
  curr_iter::Int,
  scheduler::AbstractScheduler,
  params::SaturationParams,
  report::SaturationReport,
  ematch_buffer::OptBuffer{UInt128},
)

  setiter!(scheduler, curr_iter)

  @timeit report.to "Search" eqsat_search!(g, theory, scheduler, report, ematch_buffer)

  @timeit report.to "Apply" eqsat_apply!(g, theory, report, params, ematch_buffer)

  if report.reason === nothing && cansaturate(scheduler) && isempty(g.pending)
    report.reason = :saturated
  end
  @timeit report.to "Rebuild" rebuild!(g; should_check_memo = params.check_memo, should_check_analysis = params.check_analysis)

  Schedulers.rebuild!(scheduler)

  @debug "Smallest expression is" extract!(g, astsize)

  return report
end

"""
Given an [`EGraph`](@ref) and a collection of rewrite rules,
execute the equality saturation algorithm.
"""
function saturate!(g::EGraph, theory::Theory, params = SaturationParams())
  curr_iter = 0

  sched = params.scheduler(g, theory; params.schedulerparams...)
  report = SaturationReport(g)

  start_time = time_ns()

  params.timer || disable_timer!(report.to)

  # Buffer for e-matching. Use a local buffer for generated functions.
  ematch_buffer = OptBuffer{UInt128}(64)

  while true
    curr_iter += 1

    @debug "================ EQSAT ITERATION $curr_iter  ================"
    @debug g

    report = eqsat_step!(g, theory, curr_iter, sched, params, report, ematch_buffer)

    elapsed = time_ns() - start_time

    if params.goal(g)
      @debug "Goal reached"
      report.reason = :goalreached
      break
    end

    if report.reason !== nothing
      @debug "Reason" report.reason
      break
    end

    if params.timelimit > 0 && params.timelimit <= elapsed
      @debug "Time limit reached"
      report.reason = :timelimit
      break
    end

    if curr_iter >= params.timeout
      @debug "Too many iterations"
      report.reason = :timeout
      break
    end

    if params.eclasslimit > 0 && length(g.classes) > params.eclasslimit
      @debug "Too many eclasses"
      report.reason = :eclasslimit
      break
    end
  end
  report.iterations = curr_iter

  return report
end
