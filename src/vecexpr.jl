module VecExprModule

export Id,
  VecExpr,
  VECEXPR_FLAG_ISTREE,
  VECEXPR_FLAG_ISCALL,
  VECEXPR_META_LENGTH,
  v_new,
  v_flags,
  v_unset_flags!,
  v_check_flags,
  v_set_flag!,
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
  v_set_signature!,
  v_pair,
  v_pair_first,
  v_pair_last

const Id = UInt64

"""
    struct VecExpr
      data::Vector{Id}
    end

An e-node is represented by `Vector{Id}` where:
* Position 1 stores the hash of the `VecExpr`.
* Position 2 stores the bit flags (`isexpr` or `iscall`).
* Position 3 stores the signature
* Position 4 stores the hash of the `head` (if `isexpr`) or node value in the e-graph constants.
* The rest of the positions store the e-class ids of the children nodes.

The expression is represented as an array of integers to improve performance.
The hash value for the VecExpr is cached in the first position for faster lookup performance in dictionaries.

"""
mutable struct VecExpr
  hash::Id
  const flags::Id
  const signature::Id
  head::Id # TODO this is changed between quoted and unquoted hash at a few points (mainly because patterns store nodes themselves)
  const children::Vector{Id}
end

const VECEXPR_FLAG_ISTREE = 0x01
const VECEXPR_FLAG_ISCALL = 0x10
const VECEXPR_META_LENGTH = 4

v_flags(n::VecExpr)::Id = n.flags
# v_unset_flags!(n::VecExpr) = n.flags = 0
v_check_flags(n::VecExpr, flag::Id)::Bool = !iszero(v_flags(n) & flag)
# v_set_flag!(n::VecExpr, flag)::Id = n.flags |= flag

"""Returns `true` if the e-node ID points to a an expression tree."""
v_isexpr(n::VecExpr)::Bool = !iszero(v_flags(n) & VECEXPR_FLAG_ISTREE)

"""Returns `true` if the e-node ID points to a function call."""
v_iscall(n::VecExpr)::Bool = !iszero(v_flags(n) & VECEXPR_FLAG_ISCALL)

"""Number of children in the e-node."""
v_arity(n::VecExpr)::Int = length(n.children)

"""
Compute the hash of a `VecExpr` and store it as the first element.
"""
function v_hash!(n::VecExpr)::Id
  if iszero(n.hash)
    n.hash = hash(n.flags, hash(n.signature, hash(n.children, n.head)))
  else
    # h = hash(@view n[2:end])
    # @assert h == n[1]
    n.hash
  end
end

# """The hash of the e-node."""
v_hash(n::VecExpr)::Id = n.hash
Base.hash(n::VecExpr, h::UInt) = hash(v_hash(n), h)
Base.:(==)(a::VecExpr, b::VecExpr) = a.signature == b.signature && a.head == b.head && a.flags == b.flags && a.children == b.children

"""Set e-node hash to zero."""
v_unset_hash!(n::VecExpr)::Id = n.hash = Id(0)

"""E-class IDs of the children of the e-node."""
v_children(n::VecExpr) = n.children

v_signature(n::VecExpr)::Id = n.signature

# v_set_signature!(n::VecExpr, sig::Id) = n.signature = sig

"The constant ID of the operation of the e-node, or the e-node ."
v_head(n::VecExpr)::Id = n.head

"Update the E-Node operation ID."
v_set_head!(n::VecExpr, h::Id) = n.head = h

"""Construct a new, empty `VecExpr` with `len` children."""
function v_new(is_tree, is_call, signature, head, num_children::Int)::VecExpr
  flags = (is_tree ? VECEXPR_FLAG_ISTREE : 0) | (is_call ? VECEXPR_FLAG_ISCALL : 0)
  VecExpr(Id(0), flags, signature, head, Array{Id}(undef, num_children))
end

v_children_range(n::VecExpr) = eachindex(n.children)


# TODO tuple should be as fast as this
v_pair(a::UInt64, b::UInt64) = UInt128(a) << 64 | b
v_pair_first(p::UInt128)::UInt64 = UInt64(p >> 64)
v_pair_last(p::UInt128)::UInt64 = UInt64(p & 0xffffffffffffffff)

# Base.length(n::VecExpr) = length(n.data)
# Base.getindex(n::VecExpr, i) = n.data[i]
# Base.setindex!(n::VecExpr, val, i) = n.data[i] = val
Base.copy(n::VecExpr) = VecExpr(n.hash, n.flags, n.signature, n.head, copy(n.children))
# Base.lastindex(n::VecExpr) = lastindex(n.data)
# Base.firstindex(n::VecExpr) = firstindex(n.data)

# Base.isless(a::VecExpr, b::VecExpr) = isless(a.data,b.data)
Base.isless(a::VecExpr, b::VecExpr) = error("not implemented")

end
