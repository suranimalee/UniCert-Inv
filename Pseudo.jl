#####################################################################
#
#               pseudo_hnf for a column matrix
#
#####################################################################

function mult_col(M::Generic.Mat{T}, i::Int, r::T) where T
    for j in 1:nrows(M)
        M[j, i] = M[j, i]*r
    end
    return nothing
end

# pseudo_TransTwo computes coefficient_ideals and inverse transformation matrix of hnf of a column matrix.
function pseudo_TransTwo(B::Hecke.PMat)
   H = deepcopy(B)
   m = nrows(H)
   n = ncols(H)
   A = H.matrix
   K = base_ring(A)
   T = MatrixSpace(K,m,m)(K(1))  
   t1 = K()
   t2 = K()
   tt = K() 
   k = 1
   i = 1
      j = k
      while j <= m && A[j, i] == 0
         j += 1
      end

      if j > k
         swap_rows!(H, j, k)
      end
      H.coeffs[k] == H.coeffs[k]*A[k, i]
      simplify(H.coeffs[k])
      mult_col(T, k, A[k, i])   
      Hecke.divide_row!(A, k, A[k, i])

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
            t = deepcopy(T[c, k])
            mul!(tt, T[c, j], Aji)
            addeq!(T[c, k], tt)
            mul!(t1, t, -u) 
            mul!(t2, T[c, j], v)
            T[c, j]=t1+t2
         end
         H.coeffs[j] = a*b//d
         simplify(H.coeffs[j])
         H.coeffs[k] = d
         simplify(H.coeffs[k])
      end
   return H.coeffs, T 
end


#####################################################################
#
#           Inverse computation
#
#####################################################################


# inverse computation of a non-singular matrix over number fields, using linear lifting.
function InvLift(A::Generic.Mat{nf_elem}) 
p = Hecke.next_prime(Hecke.p_start)
n = nrows(A)
K = Hecke.base_ring(A)
I = MatrixSpace(K,n,n)(K(1))

me = Hecke.modular_init(K, fmpz(p))
ap = Hecke.modular_proj(A, me)
AA = Hecke.modular_lift(ap, me)
 d = det(AA)
pp = fmpz(p)
    if d==0
        error("bad prime")
    else
        ap = [inv(x) for x= ap]
        B = Hecke.modular_lift(ap, me)
        iA = deepcopy(B)
        I = MatrixSpace(K,n,n)(1)
        R = (I-A*B)*(1//p)
i=1
        while true
i+=1
            M = Hecke.modular_lift(Hecke.modular_proj(B*R, me), me)
            R = (R-A*M)*(1//p)
            iA += M*pp
            pp *= p
            fl, IA= rational_reconstruction2_copy(iA,pp) #rational_reconstruction(iA,pp) 
                if fl && A*IA==I
                    println("inv-lift: $i")
                    return IA
                end
        end
    end
end



# FAST- inverse computation of a upper-triangular matrix
function inv_upper_triang(M::Generic.Mat{T}) where T
K = base_ring(M)
n = nrows(M)
I=MatrixSpace(K,n,n)(K(1))
    for i= 1:n
        I[i, i] = 1//M[i, i]
        for j = i+1 :n
#TODO wrire as a sum
            for k= i: j-1
                I[i,j]+=I[i, k]*M[k ,j]
            end
            I[i, j] = (-I[i,j]//M[j, j])
        end
    end
    return I
end


# SLOWER -inverse computation of a upper-triangular matrix
function inv_upper_triang_two(A::Generic.Mat{T}) where T
M = deepcopy(A)
K = base_ring(M)
n = nrows(M)
I = MatrixSpace(K,n,n)(K(1))
J = MatrixSpace(K,n,n)(K(1))
O = MatrixSpace(K,n,n)(K(0))
    for i = 1: n
        J[i, i] = 1//M[i, i]
        M[i, i] = K(0)   
    end
    JM=-J*M
    TT= JM
    while TT!=O
        I += TT
        TT *= JM
    end
    return I*J
end


#################################################################
#
#                   Denominator of a PMat
#
#################################################################

#FAST- denominator computation of a PMat
function Denom(P::Hecke.PMat)
    l = fmpz(1)
    p = matrix(P)
    C = coefficient_ideals(P)
    for i=1:nrows(P)
        I = coefficient_ideals(P)[i]
        Hecke.assure_2_normal(I.num)
        t1 = I.num.gen_one
        t2 = I.num.gen_two.elem_in_nf
        for j=1:ncols(P)
            fl = !isone(denominator(t1*p[i,j]))
            fll = !isone(denominator(t2*p[i,j])) 
            if fl || fll
                return false
            end 
        end
    end
    return true
end



#SLOWER- denominator computation of a PMat
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



####################################################
#               Dual
###################################################


function Hecke.dual(P::Hecke.PMat)
    return pseudo_matrix(inv(P.matrix)', map(inv, coefficient_ideals(P)))
end

####################################################
#               Copy of RatRecon
###################################################

function rational_reconstruction2_copy(A::Generic.Mat{nf_elem}, M::fmpz)
    B = similar(A)
    sM = root(M, 2)
    d = one(A[1,1])
    di = inv(d)
    for i=1:nrows(A)
        for j=1:ncols(A)
            a = A[i,j]*d
            mod_sym!(a, M)
            if all(i->Hecke.small_coeff(a, sM, i), 1:a.elem_length)
                B[i,j] = a*di
            else
                n, dn = Hecke.algebraic_reconstruction(a, M)
                d*=dn
                if any(i->!Hecke.small_coeff(d, sM, i), 1:a.elem_length)
                    println("early $i $j abort")
                    return false, B
                end
                di*=inv(dn)
                B[i,j] = n*di
            end
        end
    end
    println("final den: $d")
    return true, B
end



####################################################################
#
#               Determinant of a matrix over number field
#
####################################################################


## CRT
function crt_ideal(A::NfOrdIdl, B::NfOrdIdl, a::NfOrdElem, b::NfOrdElem )
    v,u=idempotents(A,B)
    return a*u+b*v
end

# Entries of the Matrix $A$ are given as an array

function array_mat(A::MatElem{T}) where T
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
	push!(a, numerator(A[i,j]))
     end
   end
  return a
end


## Determinant computing using CRT with determinant-ideal "D" ( from PseudoDet)
function determinant_test(D::NfAbsOrdIdl{AnticNumberField,nf_elem}, A::Generic.Mat{nf_elem})
    K=base_ring(A)
    d=degree(K)
    ZK=maximal_order(K)
    p=next_prime(Hecke.p_start)
    t=0
    PP=fmpz(1)
    Dl =lll(basis_matrix(D))
    U = matrix(QQ,degree(K),degree(K),array_mat(Dl))
    F = []
    for i=1:nrows(Dl)
         push!(F, order(D)([Dl[i,j] for j=1:ncols(Dl)]))
    end
    de = ZK(0)
    d1 = ZK(0)

    while true
        me = Hecke.modular_init(K, p)
        ap = Hecke.modular_proj(A, me)
        ap = [det(x) for x= ap]
        Aip= Hecke.modular_lift(ap, me)
@show t+=1
        de = crt_ideal(D,ideal(ZK, p) ,de, ZK(Aip))
        D*=p
        PP*=p
        TT=coordinates(de)
        V=matrix(QQ,degree(K),1,TT)
        W=Hecke.solve(U',V)
        W=(1//PP)*W
        k=0
        for j=1:degree(K)
            k += F[j]*(round(fmpz,(W[j,1])))
        end
        k=PP*k
        de= de-k
        if d1==de
            return de 
        else
            d1=de
            p = next_prime(p)
        end
    end
end




#####################################################################
#
#               Determinant ideal 2
#
#####################################################################

# Example  : @time PseudoDetTwo(m, 100:1000)

function ExtendTwo(M::Hecke.PMat, b::Generic.MatSpaceElem{nf_elem}, gamma::Generic.MatSpaceElem{nf_elem})
    zk = base_ring(M)
    p = pseudo_matrix(gamma, vcat( [1*zk], map(inv, coefficient_ideals(M))))
    println("HNF")
    @time   h, T = pseudo_TransTwo(p)
    e = pseudo_matrix((T'*hcat(b, M.matrix')')[2:nrows(M)+1, :], map(inv, h[2:nrows(M)+1]))
    println("dual")
    @time   d =pseudo_matrix(inv(e.matrix'), h[2:nrows(M)+1])
    return e, d
end

function PseudoDetTwo(A::Generic.Mat{nf_elem}, U::UnitRange{Int64}) 
    K = base_ring(A)
    n = ncols(A)
    b = rand(MatrixSpace(K, n, 1), U)
    #  S = kernel(hcat(A, b));
    S = Hecke.solve_dixon(A,b)
    I = MatrixSpace(K,1,1)(1)
    S = vcat(I, -S)
    println("Extend")
    m1, d = ExtendTwo(pseudo_matrix(A'), b, S)
    D = false
tt=0
    while true
        println("Denom")
        @time D= Denom(d)
        if D
            P=prod(coefficient_ideals(d))
            return  determinant_test(integral_split(P)[1],A) 
        end
@show tt+=1
        b = rand(MatrixSpace(K, n, 1), U)   
        # S = kernel(hcat(m1.matrix', b));
        S = solve(m1.matrix',b)
        I = MatrixSpace(K,1,1)(1)
        S = vcat(I, -S)
        m1,d = ExtendTwo(m1, b, S)
    end
end


###################################################################
#
#               Determinant ideal 1
# (Sherman-Morrison formula)
##################################################################

# Example :  @time PseudoDet(m, 100:1000)

function PseudoDet(A::Generic.Mat{nf_elem}, U::UnitRange{Int64}) 
    K = base_ring(A)
    n = ncols(A)
    b = rand(MatrixSpace(K, n, 1), U)
    zk = maximal_order(K)
#TODO compute inv and replace solver
    gamma = Hecke.solve_dixon(A,b)
    I = MatrixSpace(K,1,1)(1)
    S = vcat(I, -gamma)
    M = pseudo_matrix(A')
    p = pseudo_matrix(S, vcat( [1*zk], map(inv, coefficient_ideals(M))))
    println("HNF")
    @time    h, Ti = pseudo_TransTwo(p)
    m1 = pseudo_matrix((Ti[2:n+1,2:n+1]'*A' + Ti[1:1, 2:n+1]'*b'), map(inv, h[2:n+1]))
    println("dual")
    @time begin
    C = inv(Ti[2:n+1,2:n+1]'*A')
    u = Ti[1:1, 2:n+1]
    c = inv( 1+(b'*C*u')[1,1])
    d = pseudo_matrix((C- c*C*u'*b'*C)',  h[2:n+1])
    end 
    D = false    
tt=0
    while true
        println("Denom")
        @time D = Denom(d)
        if D
            P=prod(h[2:n+1])
            return  determinant_test(integral_split(P)[1],A) 
        end
@show tt+=1
        b = rand(MatrixSpace(K, n, 1), U)   
        gamma = (d.matrix)*b #solve(m1.matrix',b)
        S = vcat(I, -gamma)
        println("HNF")
        @time p = pseudo_matrix(S, vcat( [1*zk], map(inv, coefficient_ideals(m1))))
        h, Ti = pseudo_TransTwo(p)
        m1 = pseudo_matrix((Ti[2:n+1,2:n+1]'*m1.matrix + Ti[1:1, 2:n+1]'*b'), map(inv, h[2:n+1]))
        println("dual")
        @time begin
       # C = (d.matrix)'*inv(Ti[2:n+1,2:n+1]')
        println("inv-tri")
        @time  C = (d.matrix)'*(inv_upper_triang(Ti[2:n+1,2:n+1]))'
        u = Ti[1:1, 2:n+1]
        c = inv( 1+(b'*C*u')[1,1])
        println("Sherman")
        @time  d = pseudo_matrix((C- c*C*u'*b'*C)',  h[2:n+1])
        end
    end
end



#= example

Zx,x=FlintZZ["x"]
k,a=number_field(x^3+7x+1)
m = rand(MatrixSpace(k,10,10),100:1000);
m = cat(m,m, dims=(1,2));

include("/home/ajantha/Documents/Determinant/Pseudo.jl")
@time PseudoDetTwo(m, 100:1000); # 100:1000 is the input size
@time PseudoDet(m, 100:1000);

=#

