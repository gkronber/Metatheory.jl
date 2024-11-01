module VecExprModule

export Id,
  VecExpr,
  VECEXPR_FLAG_ISTREE,
  VECEXPR_FLAG_ISCALL,
  v_new_expr, v_new_literal,
  v_flags,
  v_isexpr,
  v_iscall,
  v_head,
  v_set_head!,
  v_children,
  v_children_range,
  v_arity,
  v_hash!,
  v_hash,
  v_unset_hash!,
  v_signature,
  v_pair,
  v_pair_first,
  v_pair_last

const Id = UInt64

"""
    struct VecExpr
      hash::Id
      const flags::Int8
      const signature::Id
      head::Id
      const children::Vector{Id}
    end

An e-node is represented by `Vector{Id}` where:
* hash of the `VecExpr`.
* bit flags (`isexpr` or `iscall`).
* the signature is combines the operation and its arity using a hash
* the hash of the `head` (if `isexpr`) or node value in the e-graph constants.
* The vector of children store the e-class ids of the children nodes.

The hash value for the VecExpr is cached in the first position for faster lookup performance in dictionaries.

"""
mutable struct VecExpr
  hash::UInt64
  const flags::Int8
  const signature::UInt64
  head::Id # TODO this is changed between quoted and unquoted hash at a few points (mainly because patterns store nodes themselves)
  const children::Vector{Id}
end

const VECEXPR_FLAG_ISTREE = 0x01
const VECEXPR_FLAG_ISCALL = 0x10

v_flags(n::VecExpr)::Int8 = n.flags

"""Returns `true` if the e-node ID points to a an expression tree."""
v_isexpr(n::VecExpr)::Bool = !iszero(v_flags(n) & VECEXPR_FLAG_ISTREE)

"""Returns `true` if the e-node ID points to a function call."""
v_iscall(n::VecExpr)::Bool = !iszero(v_flags(n) & VECEXPR_FLAG_ISCALL)

"""Number of children in the e-node."""
v_arity(n::VecExpr)::Int = length(n.children)

"""
Compute the hash of a `VecExpr` and store it as the first element.
"""
function v_hash!(n::VecExpr)
  if iszero(n.hash)
    n.hash = hash(n.flags, hash(n.signature, hash(n.children, n.head)))
  else
    # h = hash(@view n[2:end])
    # @assert h == n[1]
    n.hash
  end
end

# """The hash of the e-node."""
v_hash(n::VecExpr) = n.hash
Base.hash(n::VecExpr, h::UInt) = hash(v_hash(n), h)
Base.:(==)(a::VecExpr, b::VecExpr) = a.signature == b.signature && a.head == b.head && a.flags == b.flags && a.children == b.children

"""Set e-node hash to zero."""
v_unset_hash!(n::VecExpr) = n.hash = 0

"""E-class IDs of the children of the e-node."""
v_children(n::VecExpr) = n.children
v_children_range(n::VecExpr) = eachindex(n.children)

v_signature(n::VecExpr) = n.signature

"The constant ID of the operation of the e-node, or the e-node ."
v_head(n::VecExpr)::Id = n.head

# TODO try to make this constant
"Update the E-Node operation ID."
v_set_head!(n::VecExpr, h::Id) = n.head = h

"""Construct a new, empty `VecExpr` for an expression with `num_children` children."""
function v_new_expr(is_call, signature, head, num_children::Int)::VecExpr
  flags = VECEXPR_FLAG_ISTREE | (is_call ? VECEXPR_FLAG_ISCALL : 0)
  VecExpr(0, flags, signature, head, Array{Id}(undef, num_children))
end

"""Construct a new, empty `VecExpr` representing a literal."""
function v_new_literal(head)::VecExpr
  VecExpr(0, Int8(0), 0, head, Array{Id}(undef, 0))
end

Base.copy(n::VecExpr) = VecExpr(n.hash, n.flags, n.signature, n.head, copy(n.children))

# TODO tuple should be as fast as this
v_pair(a::UInt64, b::UInt64) = UInt128(a) << 64 | b
v_pair_first(p::UInt128)::UInt64 = UInt64(p >> 64)
v_pair_last(p::UInt128)::UInt64 = UInt64(p & 0xffffffffffffffff)

end
