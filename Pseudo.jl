# Example: denominatorDet computes a unimodular pseudo-matrix, by applying transformation to the pseudo-matrix of A. U: is the range of input size.  
#julia> include("/home/ajantha/Documents/Determinant/PseudoTwo.jl")
#julia> denominatorDet(A,1:10)


function denominatorDet(A::Generic.Mat{nf_elem}, U::UnitRange{Int64}) 
    K = base_ring(A)
    n = ncols(A)
    b = rand(MatrixSpace(K, n, 1), U)
    zk = maximal_order(K)
    gamma = solve(A,b)
    I = MatrixSpace(K,1,1)(1)
    S = vcat(I, -gamma)
    M = pseudo_matrix(A')
    p = pseudo_matrix(S, vcat( [1*zk], map(inv, coefficient_ideals(M))))
println("HNF")
    h, T = pseudo_TransTwo(p)
println("Extend")
@time  Ti = inv(T)
    m1 = pseudo_matrix((Ti[2:n+1,2:n+1]'*A' + Ti[1:1, 2:n+1]'*b'), map(inv, h[2:n+1]))
println("dual")
@time begin
        C = inv(Ti[2:n+1,2:n+1]'*A')
        u = Ti[1:1, 2:n+1]
        c =inv( 1+(b'*C*u')[1,1])
        d = pseudo_matrix((C- c*C*u'*b'*C)',  h[2:n+1])
end     
    tt=0
    while true
@show   D= Denominator(d)
#@time dual(m1)#)
        if isone(D)
            return  m1 
        end
@show tt+=1
        b = rand(MatrixSpace(K, n, 1), U)      
        gamma = (d.matrix)*b #solve(m1.matrix',b)
        S = vcat(I, -gamma)
        p = pseudo_matrix(S, vcat( [1*zk], map(inv, coefficient_ideals(m1))))
        h, T = pseudo_TransTwo(p)
        Ti = inv(T)
        m1 = pseudo_matrix((Ti[2:n+1,2:n+1]'*m1.matrix + Ti[1:1, 2:n+1]'*b'), map(inv, h[2:n+1]))
println("dual")
@time begin
        C = (d.matrix)'*inv(Ti[2:n+1,2:n+1]')
        u = Ti[1:1, 2:n+1]
        c =inv( 1+(b'*C*u')[1,1])
        d = pseudo_matrix((C- c*C*u'*b'*C)',  h[2:n+1])
    end
end
end






###############################################
function Extend(M::Hecke.PMat, b::Generic.MatSpaceElem{nf_elem}, gamma::Generic.MatSpaceElem{nf_elem})
    K = base_ring(gamma)
    zk = maximal_order(K)
    n = nrows(M)
    I = MatrixSpace(K,1,1)(1)
    S = vcat(I, -gamma)
    p = pseudo_matrix(S, vcat( [1*zk], map(inv, coefficient_ideals(M))))
println("HNF")
    h, T = pseudo_TransTwo(p)
println("inv")
@time  Ti = inv(T)
    e = pseudo_matrix((Ti[2:n+1,2:n+1]'*M.matrix + Ti[1:1, 2:n+1]'*b'), map(inv, h[2:n+1]))
@time begin
    C = inv(Ti[2:n+1,2:n+1]'*M.matrix)
    u = Ti[1:1, 2:n+1]
    c =inv( 1+(b'*C*u')[1,1])
    d = pseudo_matrix((C- c*C*u'*b'*C)',  h[2:n+1])
end
    return e ,d
end



########### Denominator #######################
function Denominator(P::Hecke.PMat)
  l = fmpz(1)
  p = matrix(P)
  for i=1:nrows(P)
    I = coefficient_ideals(P)[i]
    Hecke.assure_2_normal(I.num)
    for j=1:ncols(P)
      l = lcm(l, denominator(simplify(p[i,j]*I)))
    end
  end
  return l
end


function SimplifyCopy(P::Hecke.PMat)
  c = copy(coefficient_ideals(P))
  m = deepcopy(matrix(P))
  for i=1:length(c)
    #a, b = Hecke.reduce_ideal2(c[i])
    a, b = reduce_idealCopy(c[i])
    m[i, :] *= inv(b)
    c[i] = fractional_ideal(order(a), a)
  end
  return pseudo_matrix(m, c)
end



function Hecke.dual(P::Hecke.PMat)
  return pseudo_matrix(inv(P.matrix)', map(inv, coefficient_ideals(P)))
end




####################
function reduce_idealCopy(A::Hecke.NfAbsOrdFracIdl{AnticNumberField,nf_elem})
#(A::NfOrdFracIdl)
  B = inv(A)
  b = Hecke._short_elem(B.num)
  C = divexact(b, B.den)*A
  simplify(C)
  @assert C.den == 1
  return C.num, b
end



function pseudo_TransTwo(B::Hecke.PMat)
   H = deepcopy(B)
   m = nrows(H)
   n = ncols(H)
   A = H.matrix
   K = base_ring(A)
    I = MatrixSpace(K,m,m)(K(1))
   U = MatrixSpace(K,m,m)(K(1))
   t = K()
   t1 = K()
   t2 = K()
   k = 1
   i = 1
      j = k
      while j <= m && A[j, i] == 0
         j += 1
      end

      if j > k
         swap_rows!(H, j, k)
         swap_rows!(U, j, k) 
      end
# A[k,i] This step doesn't do any thing, but removing this step gives a different U
      H.coeffs[k] == H.coeffs[k]*A[k, i]
      simplify(H.coeffs[k])
      Hecke.divide_row!(U, k, A[k, i]) 
@show U==I
#@show A
      Hecke.divide_row!(A, k, A[k, i])
@show A==B.matrix
      for j = k+1:m
         if iszero(A[j, i])
            continue
         end
         Aji = deepcopy(A[j, i])
         a = H.coeffs[j]
         aa = Aji*a
         b = H.coeffs[k]
         d = aa + b
         ad = aa//d
         simplify(ad)
         bd = b//d
         simplify(bd)
         if ad.den != 1 || bd.den != 1
            error("Ideals are not integral.")
         end
         u, v = map(K, idempotents(ad.num, bd.num))
         u = divexact(u, Aji)

        
         for c = 1:m
            t = deepcopy(U[j, c])
            mul!(t1, U[k, c], -Aji)
            addeq!(U[j, c], t1)
            mul!(t1, t, u)
            mul!(t2, U[k, c], v)
            add!(U[k, c], t1, t2)
         end
      
         H.coeffs[j] = a*b//d
         simplify(H.coeffs[j])
         H.coeffs[k] = d
         simplify(H.coeffs[k])
      end

   return H.coeffs, U
end




