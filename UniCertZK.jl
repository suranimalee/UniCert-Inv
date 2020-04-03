# ZZ Random upper triangular matrix of det(A)= 1; A=RandUpperMatZ(5,1:(100))

function RandUpperMatZ(k::Int64, U::AbstractArray)
A=rand(MatrixSpace(ZZ,k,k),U)
A[1,1]=1
    for i=2:k
        A[i,i]=1
        for j=1:i-1
            A[i,i-j]=0
        end
    end
return A
end


# K-number field;  A=RandUpperMat(K,5,1:(100)) with det(A)=1
function RandUpperMat(K::AnticNumberField, k::Int64, U::AbstractArray)
A=rand(MatrixSpace(K,k,k),U)
A[1,1]=1
    for i=2:k
        A[i,i]=1
            for j=1:i-1
                A[i,i-j]=0
            end
    end
return A
end



function array_mat(A::fmpz_mat)
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
    push!(a, A[i,j])
     end
   end
return a
end

function array_mat(A::fmpq_mat)
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
    push!(a, A[i,j])
     end
   end
return a
end


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


# Unimodular Certification for Integer Matrices using Linear Lifting
# D=A*A'
# UniCert(D,13,11)
# UniCert(D, p: prime ,k: # of steps)
function UniCert(A::fmpz_mat, p::Int64, r::Int64)
n = nrows(A)
RR = ResidueRing(FlintZZ,p)
W = MatrixSpace(RR,n,n)
B = lift(inv(W(A)))
AB = matrix(QQ,n,n,array_mat(A*B))
I = MatrixSpace(QQ,n,n)(1)
R = (I-AB)*(1//p)
B = matrix(QQ,n,n,array_mat(B))

    for i=1:r
@show i
        BR = matrix(ZZ,n,n,array_mat(B*R))
        C = lift(W(BR))
        AC = matrix(QQ,n,n,array_mat(A*C))
@show   R = (R-AC)*(1//p)
    end
end


# Unimodular certification for matrices over Number Fields using Linear Lifting
# G=A*A'
# UniCert(G,13,11)
# UniCert(G,p: prime ,k: # of steps)

function UniCert(A::Generic.Mat{nf_elem}, p::Int64, k::Int64)
#p = Hecke.next_prime(Hecke.p_start)
p = Hecke.next_prime(p)
n = nrows(A)
K = Hecke.base_ring(A)

me = Hecke.modular_init(K, fmpz(2))
ap = Hecke.modular_proj(A, me)
AA = Hecke.modular_lift(ap, me)
@show   d = det(AA)

    if d==0
        return false
    else
        me = Hecke.modular_init(K, fmpz(p))
        ap = Hecke.modular_proj(A, me)
        ap = [inv(x) for x= ap]
        B = Hecke.modular_lift(ap, me)

        I=MatrixSpace(K,n,n)(1)
        @show R=(I-A*B)*(1//p)

        for i=1:k
            @show i
            M = Hecke.modular_lift(Hecke.modular_proj(B*R, me), me)
            @show R = (R-A*M)*(1//p)
        end
    end
end



#UniCert for integer matrices using Quadrstic lifting Storjohan
# k: # of steps
function UniCertQ(A::fmpz_mat, k::fmpz)
n = nrows(A)
p = Hecke.next_prime(Hecke.p_start)
d = det(mod(A,fmpz(2)))
O = MatrixSpace(QQ,n,n)(0)

  if d==0
    return false
  else

  RR = ResidueRing(FlintZZ,p)
  W = MatrixSpace(RR,n,n)

  B = lift(inv(W(A)))
  AB = matrix(QQ,n,n,array_mat(A*B))
  I = MatrixSpace(QQ,n,n)(1)
  R = (I-AB)*(1//p)

        for i=0:k-1
            R = matrix(ZZ,n,n,array_mat(R))
            T = R^2
            M = lift(W(B*T))
            MM = matrix(QQ,n,n,array_mat(T-A*M))
            R = (MM)*(1//p) 

            if R==O
                return true
            else
                continue
            end
        end
            return false
   end
end



#UniCert for matrices over number fields using Quadrstic lifting Storjohan
# k: # of steps
function UniCert(A::Generic.Mat{nf_elem}, k::Int64)
p = Hecke.next_prime(Hecke.p_start)
n = nrows(A)
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

O = MatrixSpace(K,n,n)(0)
me = Hecke.modular_init(K, fmpz(p))
ap = Hecke.modular_proj(A, me)
ap = [inv(x) for x= ap]
B = Hecke.modular_lift(ap, me)

I = MatrixSpace(K,n,n)(1)
R = MatrixSpace(K,n,n)
R = (I-A*B)*(1//p)

    for i=0:k-1
        T = R*R
        N = Hecke.modular_proj(B*T, me)
        M = Hecke.modular_lift(N, me)
        R = (T-A*M)*(1//p)
@show i
        if R==O
            return true
        else
            continue
        end
    end
    return false
 end
end


#Inverse computation Linear Lifting

function InvLift(A::Generic.Mat{nf_elem}) #, p::Int64, k::Int64
p = Hecke.next_prime(Hecke.p_start)
#p = Hecke.next_prime(p)
n = nrows(A)
K = Hecke.base_ring(A)
I = MatrixSpace(K,n,n)(K(1))

me = Hecke.modular_init(K, fmpz(2))
ap = Hecke.modular_proj(A, me)
AA = Hecke.modular_lift(ap, me)
 d = det(AA)
pp = fmpz(p)

    if d==0
        return false
    else
        me = Hecke.modular_init(K, fmpz(p))
        ap = Hecke.modular_proj(A, me)
        ap = [inv(x) for x= ap]
        B = Hecke.modular_lift(ap, me)
        iA = deepcopy(B)

        I = MatrixSpace(K,n,n)(1)
        R = (I-A*B)*(1//p)


i=1
 #       for i=1:k
        while true
@show i+=1
            M = Hecke.modular_lift(Hecke.modular_proj(B*R, me), me)
            R = (R-A*M)*(1//p)
            iA += M*pp
            pp *= p
            fl, IA= rational_reconstruction2_copy(iA,pp) #rational_reconstruction(iA,pp) 
                if fl && A*IA==I
                    return IA
                end
        end
    end
end
