# Doesnt work except for uni modular mats
# InvQuadLift(A) matrices over number fields using Quadratic lifting Storjohan
# k: # of steps
function InvQuadLift(A::Generic.Mat{nf_elem})
p = Hecke.next_prime(Hecke.p_start)
n = nrows(A)
p=fmpz(31)
#@show  p = Hecke.next_prime(fmpz(ceil(max(10000,3.61*n^2*abs(norm(det(A)))))))	
K = Hecke.base_ring(A)
d = degree(K)
me = Hecke.modular_init(K, fmpz(2))
ap = Hecke.modular_proj(A, me)
AA = Hecke.modular_lift(ap, me)
d = det(AA)
    if d==0
        return false
    else
    me = Hecke.modular_init(K, fmpz(p))
    ap = Hecke.modular_proj(A, me)
    ap = [inv(x) for x= ap]
    B = Hecke.modular_lift(ap, me)
    pp = fmpz(p)
    iA = deepcopy(B)
    I = MatrixSpace(K,n,n)(1)
    R = (I-A*B)*(1//p)
i=1
        while true
            T = R*R
            M = Hecke.modular_lift(Hecke.modular_proj(B*T, me), me)
            iA += iA*(I+R*pp)+M*pp^2
            pp = pp^2*p           
            fl, IA= rational_reconstruction2_copy(iA,pp) #rational_reconstruction(iA,pp) 

                if fl && A*IA ==I
                    return IA
                end
            R = (T-A*M)*(1//p)
@show i+=1
        end
            return false
    end
end





function rational_reconstruction_ZMat(A::fmpz_mat, M::fmpz)
  n = nrows(A)
  m = ncols(A)    
  B = zero_matrix(QQ,n,m)
  for i=1:n
    for j=1:m
      fl,a,b  = rational_reconstruction(A[i,j], M)
      B[i,j] = a//b
      if !fl 
        return false, B
      end
    end
  end
  return true, B
end


# Doesnt work except for uni modular mats
# InvQuadLift for integer matrices using Quadrstic lifting Storjohan
# k: # of steps
function InvQuadLift(A::fmpz_mat, k::fmpz)
n = nrows(A)
AQ = matrix(QQ,n,n,array_mat(A))
p = Hecke.next_prime(51)
d = det(mod(A,fmpz(p)))
O = MatrixSpace(QQ,n,n)(0)

    if d==0
@show first
        return false
    else

    RR = ResidueRing(FlintZZ,p)
    W = MatrixSpace(RR,n,n)
    B = lift(inv(W(A)))
    I = MatrixSpace(ZZ,n,n)(1)  
    AB = matrix(QQ,n,n,array_mat(I-A*B))
    R = (AB)*(1//p) 
    pp = fmpz(p)
    iA = deepcopy(B)

        for i=0:k-1
@show i
            R = matrix(ZZ,n,n,array_mat(R))
            T = R^2
            M = lift(W(B*T))
                iA += iA*(I+R*pp)+M*pp^2
                pp = pp^2*p           
                fl, IA= rational_reconstruction_ZMat(iA,pp) 

                if fl && AQ*IA ==I
                    return IA
                end
            MM = matrix(QQ,n,n,array_mat(T-A*M))
            R = (MM)*(1//p) 

        end
            return false
   end
end



# Quadratic Doesnt work except for uni modular mats
function InvQuad(A::fmpz_mat, p::Int64, k::Int64)
n = nrows(A)
AQ = matrix(QQ,n,n,array_mat(A))
p = Hecke.next_prime(p)
d = det(mod(A,fmpz(p)))
O = MatrixSpace(QQ,n,n)(0)

    if d==0
    @show first
        return false
    else

    RR = ResidueRing(FlintZZ,p)
    W = MatrixSpace(RR,n,n)
    B = lift(inv(W(A)))
    I = MatrixSpace(ZZ,n,n)(1)  
    pp=fmpz(p)
        for i=0:k-1
@show i
            B=B*(2*I - A*B)
                pp *= pp^2           
                fl, IA= rational_reconstruction_ZMat(B,pp) 

                if fl && AQ*IA ==I
                    return IA
                end
         end
            return false
   end
end






# Doesnt work except for uni modular mats
# InvQuadLift(A) matrices over number fields using Quadratic lifting Storjohan
# k: # of steps
function InvQuad(A::Generic.Mat{nf_elem}, k::Int64)
p = Hecke.next_prime(Hecke.p_start)
n = nrows(A)
p=fmpz(31)
#@show  p = Hecke.next_prime(fmpz(ceil(max(10000,3.61*n^2*abs(norm(det(A)))))))	
K = Hecke.base_ring(A)
d = degree(K)
me = Hecke.modular_init(K, fmpz(2))
ap = Hecke.modular_proj(A, me)
AA = Hecke.modular_lift(ap, me)
d = det(AA)
    if d==0
        return false
    else
    me = Hecke.modular_init(K, fmpz(p))
    ap = Hecke.modular_proj(A, me)
    ap = [inv(x) for x= ap]
    B = Hecke.modular_lift(ap, me)
    pp = fmpz(p)
    I = MatrixSpace(K,n,n)(1)

        for i=1:k
                B=B*(2*I-A*B)
                pp *= pp^2
                fl, IA= rational_reconstruction(B,pp) #rational_reconstruction(iA,pp) 

                if fl && A*IA ==I
                    return IA
                end
@show i
        end
            return false
    end
end


