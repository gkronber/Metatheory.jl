struct UnionFind
  parents::Vector{Int64}
end

UnionFind() = UnionFind(Id[])

function Base.push!(uf::UnionFind)::Id
  l = length(uf.parents) + 1
  push!(uf.parents, l)
  l
end

Base.length(uf::UnionFind) = length(uf.parents)

function Base.union!(uf::UnionFind, i::Id, j::Id)
  uf.parents[j] = i
  i
end

# this compresses the find path
function find!(uf::UnionFind, i::Id)::Id
  # path splitting
  while i != @inbounds uf.parents[i]
    @inbounds (i, uf.parents[i]) = (uf.parents[i], uf.parents[uf.parents[i]])
    # i = uf.parents[i]
  end

  i
end

function find(uf::UnionFind, i::Id)::Id
  while i != @inbounds uf.parents[i]
    i = @inbounds uf.parents[i]
  end

  i
end
