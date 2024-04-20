# Full e-matcher
function ematch_compile(p)
  pvars = patvars(p)
  npvars = length(pvars)

  patvar_to_addr = fill(-1, npvars)

  program = Expr[]

  memsize = 1
  ematch_compile_ground!(program, memsize)
  first_nonground = memsize
  memsize += 1

  ematch_compile!(program, p, memsize, first_nonground)


  push!(prog, yield_expr(patvar_to_addr, direction))

  σ = fill(-1, memsize)
  quote
    function (g::EGraph, rule_idx::Int, root_id::Id)::Int
      n_matches = 0
      stack = Int[]
      push!(stack, 0)

      @label compute

      pc == 0 && return n_matches

      $([:(
        if pc == $i
          $code
        end
      ) for (i, code) in enumerate(prog)]...)
      ...
    end
  end

end

# ==============================================================
# Ground Term E-Matchers
# TODO explain what is a ground term
# ==============================================================

function compile_ground!(addr, ground_terms_to_addr, program, memsize, p::Any)
  if !haskey(ground_terms_to_addr, p)
    # If the instruction for searching the constant literal
    # has not already been inserted in the program: 
    # Remember that it has been searched and its stored in σ[addr]
    ground_terms_to_addr[p] = addr
    # Add the lookup instruction to the program
    push!(program, lookup_expr(addr, p))
  end
end

# Ground e-matchers
function compile_ground!(addr, ground_terms_to_addr, program, memsize, pattern::PatTerm)
  if !haskey(ground_terms_to_addr, pattern)
    # If the instruction for searching the term
    # has not already been inserted in the program:
    ground_terms_to_addr[pattern] = addr

    if isground(pattern)
      # Remember that it has been searched and its stored in σ[addr]
      ground_terms_to_addr[pattern] = addr
      # Add the lookup instruction to the program
      push!(program, lookup_expr(addr, pattern))
      # Memory needs one more register 
      memsize[] += 1
    else
      # Search for ground patterns in the children.
      for child_pattern in children(pattern)
        compile_ground!.(memsize[], ground_terms_to_addr, program, memsize, child_pattern)
      end
    end
  end
end

# ==============================================================
# Actual Instructions
# ==============================================================

function lookup_expr(addr, p)
  quote
    ecid = lookup_pat(g, $p)
    if ecid > 0
      σ[$addr] = ecid
      pc += 1
      @goto compute
    end
    @goto backtrack
  end
end

function yield_expr(patvar_to_addr, direction)

  makedict = [:(b = assoc(b, $i, (σ[$addr], n[$addr]))) for (i, addr) in enumerate(patvar_to_addr)]...
  quote
    maybelock!(g) do
      b = Bindings()
      $(makedict...)

      push!(g.buffer, assoc(b, 0, (root_id, rule_idx * $direction)))
      n_matches += 1
    end

    @goto backtrack
  end
end

# ==============================================================
# ==============================================================
# ==============================================================

# DEMO

function ematch_compiler()
  is_var_bound = fill(false, npvars)
  quote
    function ematch_rule()::Int
      n_matches = 0
      stack = Int[]
      push!(stack, 0)
      pc = 1
      options = fill(1, 3)

      @label compute

      if pc == 0
        # Return 
        return n_matches
      elseif pc == 1
        # instead of for loop
        if options[1] < num_options_1
          push!(stack, 1)
          if matches(...)
            options[1] += 1
            pc += 1
            @goto compute
          end
          options[1] += 1
          @goto backtrack
        end
        options[1] = 1 # restart from first option
        @goto backtrack
      elseif pc == 2
        ...
      elseif pc == 3
        println("success!")
        @goto backtrack
      end

      @label backtrack
      pc = pop!(stack)
      @goto compute
    end
  end
end