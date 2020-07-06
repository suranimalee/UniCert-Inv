import Hecke: valuation, divexact, parent_type, elem_type, mul!, addeq!, parent
import Base: +, -, *, ^
export RNSnf_elem



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


function bad_mat(R::Hecke.Ring, n::Int, U)
z = zero_matrix(R, n, n)
    for i=1:n-1
        z[i+1,i] = one(R)
        z[i+1, i+1] = rand(R, U)
    end
    d = one(R)
    for i=n:-1:1
        k = rand(R, U)
        z[1, i] = d+k*z[i,i]
        d = k
    end
    return z
end


function modsM(A::Generic.Mat{nf_elem}, m::fmpz)
K = base_ring(A)
B = zero_matrix(K,nrows(A),ncols(A))
    for i=1:nrows(A)
        for j=1:ncols(A)
            B[i,j] = Hecke.mod_sym(A[i, j], m)
        end
    end
    return B
end


function invmodM(A::Generic.MatSpaceElem{nf_elem}, p::fmpz)
    k = base_ring(A)
    me = Hecke.modular_init(k, fmpz(p))
    ap = Hecke.modular_proj(A, me)
    ap = [inv(x) for x= ap]
    B = Hecke.modular_lift(ap, me)
    return B
end


###################################################################
#
#            Residue Number System
#
###################################################################

mutable struct RNS <: Hecke.Ring
  p::Array{fmpz, 1}
  P::Array{fmpz, 1}
  Pi::Array{fmpz, 1}
#  w::Array{fmpq, 1}
#  c::Array{fmpz, 1}  
  r::fmpz
  N::fmpz
  ce

  function RNS(p::Array{fmpz, 1})
    s = new()
    s.p = p
    P = prod(p)
    s.P = [divexact(P, x) for x = p]
    s.Pi = [invmod(s.P[i], s.p[i]) for i = 1:length(p)]
    s.r = next_prime(2^50)
    s.N = P
    s.ce = Hecke.crt_env(p)
#    s.w = [s.Pi[i]//s.p[i] for i = 1:length(p)]
#    s.c = [s.P[i]*s.Pi[i] for i = 1:length(p)]
    return s
  end

  function RNS(p::Array{<:Integer, 1})
    return RNS(fmpz[x for x = p])
  end

  function RNS(p::Array{<:Any, 1})
    return RNS(fmpz[x for x = p])
  end
end
function Base.show(io::IO, R::RNS)
  print(io::IO, "crt ring with moduli ", R.p)
end


# RNS for number field elements
mutable struct RNSnf_elem <: Hecke.RingElem
  x::Array{nf_elem, 1}
  r::nf_elem 
  R::RNS
  function RNSnf_elem(X::RNS, a::nf_elem)
    s = new()
    s.x = [mod(a, p) for p = X.p]
    s.r = mod(a, X.r)
    s.R = X
    return s
  end


  function RNSnf_elem(X::RNS, a::Array{nf_elem, 1}, k::nf_elem)
    r = new()
    r.R = X
    r.x = a
    r.r = k
    return r
  end
end



function Base.show(io::IO, a::RNSnf_elem)
  print(io, "crt: ", a.x)
end

elem_type(::RNS) = RNSnf_elem
parent_type(::RNSnf_elem) = RNS
parent_type(::Type{RNSnf_elem}) = RNS

parent(a::RNSnf_elem) = a.R

-(a::RNSnf_elem, b::RNSnf_elem) = RNSnf_elem(a.R, [mod(a.x[i]-b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r-b.r, a.R.r))
+(a::RNSnf_elem, b::RNSnf_elem) = RNSnf_elem(a.R, [mod(a.x[i]+b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r+b.r, a.R.r))
*(a::RNSnf_elem, b::RNSnf_elem) = RNSnf_elem(a.R, [mod(a.x[i]*b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r*b.r, a.R.r))
*(a::Integer, b::RNSnf_elem) = RNSnf_elem(b.R, [mod(a*b.x[i], b.R.p[i]) for i=1:length(b.x)], mod(a*b.r, b.R.r))
divexact(a::RNSnf_elem, b::RNSnf_elem) = RNSnf_elem(a.R, [mod(a.x[i]*invmod(b.x[i], a.R.p[i]), a.R.p[i]) for i=1:length(a.x)], mod(a.r*invmod(b.r, a.R.r), a.R.r))
-(a::RNSnf_elem) = RNSnf_elem(a.R, [mod(-a.x[i], a.R.p[i]) for i=1:length(a.x)], -a.r)
#^(a::RNSnf_elem, e::Integer) = RNS_nfelem(a.R, [powmod(a.x[i], e, a.R.p[i]) for i=1:length(a.x)], powmod(a.r, e, a.R.r))
(R::RNS)() = RNSnf_elem(R, fmpz[0 for i=1:length(R.p)], fmpz(0))
(R::RNS)(a::Integer) = RNSnf_elem(R, a)
(R::RNS)(a::RNSnf_elem) = a

function addeq!(a::RNSnf_elem, b::RNSnf_elem)
  for i=1:length(a.x)
    a.x[i] = mod(a.x[i] + b.x[i], a.R.p[i])
    a.r    = mod(a.r    + b.r   , a.R.r)
  end
  return a
end

function mul!(a::RNSnf_elem, b::RNSnf_elem, c::RNSnf_elem)
  for i=1:length(a.x)
    a.x[i] = mod(b.x[i] * c.x[i], a.R.p[i])
    a.r    = mod(b.r    * c.r   , a.R.r)
  end
  return a
end

function check(a::RNSnf_elem)
    z = fmpz(a)
  @assert mod(z, a.R.r) == a.r
end

#TODO use idempotents for extend
# given x mod p_i and p_r, find x mod p 
function extend(R::RNS, a::RNSnf_elem, p::fmpz)
  k = sum((mod(a.x[i]*R.Pi[i] , R.p[i])) * mod(R.P[i] , R.r) for i=1:length(R.p)) - a.r
  k = mod(k*invmod(R.N, R.r), R.r)
#  @assert k <= length(R.p)
  return mod((sum(mod((a.x[i]*R.Pi[i]), R.p[i]) * mod(R.P[i], p) for i=1:length(R.p)) - k*mod(R.N , p)),p)
end

function mixed_radix(R::RNS, a::RNSnf_elem, li::Int = typemax(Int))
A = nf_elem[]
    for i=1:min(length(a.x), li)
        y = a.x[i]
    for j=1:i-1
        y = mod(((y-A[j])*invmod(R.p[j], R.p[i])), R.p[i])
    end
    push!(A, y)
  end
  return A
  #so a = A[1] + A[2]*p[1] + A[3]*p[1]*p[2] ...s
end

function rss_elem_from_radix(R::RNS, a::Array{nf_elem, 1})
z = nf_elem[]
q = fmpz(1)
    for i=1:length(R.p)
        push!(z, q*x[i])
        q *=R.p[i]
    end
    return z
# for reconstruction: take sum(z)
end


function gen(R::RNS, i::Int)
  p = fmpz[0 for i=1:length(R.p)]
  p[i] = fmpz(1)
  r = mod(R.P[i]*R.Pi[i], R.r)
  return RNSnf_elem(R, p, r)
end

Hecke.fmpz(a::RNSnf_elem) = Hecke.crt(a.x, a.R.ce)


###################################################################
#
#            RNS for matrices over number fields
#
###################################################################

mutable struct RNSmat <: Hecke.RingElem
  x::Array{Generic.MatSpaceElem{nf_elem},1}
  r::Generic.MatSpaceElem{nf_elem} 
  R::RNS
  function RNSmat(X::RNS, a::Generic.MatSpaceElem{nf_elem})
    s = new()
    s.x = [modsM(a, p) for p = X.p]
#    s.r = modsM(a, X.r)
    s.R = X
    return s
  end


  function RNSmat(X::RNS, a::Array{Generic.MatSpaceElem{nf_elem},1})
    r = new()
    r.R = X
    r.x = a
#    r.r = k
    return r
  end
end


function Base.show(io::IO, a::RNSmat)
    print(io, "crt: ", a.x)
end

elem_type(::RNS) = RNSmat
parent_type(::RNSmat) = RNS
parent_type(::Type{RNSmat}) = RNS

parent(a::RNSmat) = a.R 

-(a::RNSmat, b::RNSmat) = RNSmat(a.R, [modsM(a.x[i]-b.x[i], a.R.p[i]) for i=1:length(a.x)])

+(a::RNSmat, b::RNSmat) = RNSmat(a.R, [modsM(a.x[i]+b.x[i], a.R.p[i]) for i=1:length(a.x)])

*(a::RNSmat, b::RNSmat) = RNSmat(a.R, [modsM(a.x[i]*b.x[i], a.R.p[i]) for i=1:length(a.x)])

invM(a::RNSmat) = RNSmat(a.R, [invmodM(a.x[i],a.R.p[i]) for i=1:length(a.x)])

-(a::RNSmat) = RNSmat(a.R, [modsM(-a.x[i], a.R.p[i]) for i=1:length(a.x)])

QuadLift( A::RNSmat, M::RNSmat, T::RNSmat, iX :: Array{fmpz,1}) = RNSmat(A.R, [modsM(iX[i]*(T.x[i]-A.x[i]*M.x[i]), A.R.p[i]) for i=1:length(A.x)])

identM(a::RNSmat) = RNSmat(a.R, [identity_matrix(a.x[i]) for i=1:length(a.x)])
zeroM(a::RNSmat) = RNSmat(a.R, [similar(a.x[i]) for i=1:length(a.x)])

function iszeroM(a::RNSmat)
i = 1
    while true
        fl = iszero(a.x[i])
        if !fl 
            return false
        end
        if i == length(a.x)
            return true
        end
        i += 1        
    end
end


function mixed_radix(R::RNS, a::RNSmat)#, li::Int = typemax(Int))
A = Generic.MatSpaceElem{nf_elem}[]
    for i=1:length(a.x)
        y = a.x[i]
        for j=1:i-1
            y = modsM(((y-A[j])*invmod(R.p[j], R.p[i])), R.p[i])
        end
        push!(A, y)
    end
    return A
  #so a = A[1] + A[2]*p[1] + A[3]*p[1]*p[2] ...s
end

function rss_mat_from_radix(R::RNS,  x::Array{Generic.MatSpaceElem{nf_elem},1})
z = Generic.MatSpaceElem{nf_elem}[]
q = fmpz(1)
    for i=1:length(R.p)
        push!(z, q*x[i])
        q *=R.p[i]
    end
   return z
end


function extend_mix(B::RNS, a::RNSmat)
z = Generic.MatSpaceElem{nf_elem}[]
LL = mixed_radix(a.R, a)
L = rss_mat_from_radix(a.R, LL)
    for i = 1: length(B.p)
        push!(z, modsM(sum(modsM(L[j],B.p[i]) for j = 1:length(L)), B.p[i]))
    end 
    return z
end 


# converter base of "a": a.R to B

convert(B::RNS, a::RNSmat) = RNSmat(B, extend_mix(B, a) )



###########################################################################################
#
#               UniCert with RNS
#
###########################################################################################


function previous_prime(p::fmpz)
    if iseven(p)
        p = p-1
    end

    while true
        p = p-2
        fl = Hecke.isprime(p)
        if fl
            return p
        end    
    end
end


function smaller_prime(p::fmpz)
    while true
        p1 = Hecke.next_prime(numerator((p-1)//2))
        if p!=p1
            return p1
        end
        p = p1-2    
    end
end

# Given an upper bound "start ", prime numbers are generated to achive the product "bound" 
function genPrimes(start::fmpz, bound::fmpz)
    tot = fmpz(1)
    a = []
    i = 0
    while tot < bound
        i +=1
        start = smaller_prime(start)
        push!(a, start)
        tot *= start
    end
        return a, i
end


#TODO chage as C-code simple way
function p_start_mat(A:: Generic.Mat{nf_elem})
    n = nrows(A)
    return numerator(floor(fmpz(floor(sqrt(4*n*(2^53-1)+1) +(2*n-1)))//(2*n)))
end

# bound for basis P and X 
function PXbounds(A:: Generic.Mat{nf_elem}, S::Int64)
n = nrows(A)
K = Hecke.base_ring(A)
zk= lll(maximal_order(K))
c1,c2=norm_change_const(zk)
d = degree(K)
n = nrows(A)
   return   fmpz(round(1.2002*n*c1*c2*d*S)), fmpz(round(3.61*(n*c1*c2*d)^2*S))
end


#TODO check bound
# number of lifting operations in UniCert
function nLifts(A:: Generic.Mat{nf_elem}, X:: fmpz, S:: Int64)
n = nrows(A)
K = Hecke.base_ring(A)
d = degree(K)
n = nrows(A)
    if isodd(n)
        n = n+1
    end
    bound = fmpz(n^((n//2)-2)*S^(n-2))
    y = fmpz(1)
    k = 1
    while y < bound
        X = X^2
        y *= X 
        k +=1
    end
    return k
end



# Unimodular Certification for matrices over number fields

function UniCertNF(A::Generic.Mat{nf_elem}, u::Int64)
n = nrows(A)
K = Hecke.base_ring(A)
zk= lll(maximal_order(K))
c1,c2=norm_change_const(zk)
d = degree(K)
p0 = p_start_mat(A) #fmpz(100) 
PB, XB = PXbounds(A, u)
P, np = genPrimes(p0, PB)
X, nx = genPrimes(P[np], XB)
@show P = RNS(P)
@show X = RNS(X)
k = nLifts(A, X.N, u)

    iX = Array(ZZ,np)
    for i = 1 : np
       iX[i] = invmod(X.N, P.p[i])  
    end

    Ap = RNSmat(P, A)
    Ax = RNSmat(X, A)
#TODO C-code check existence
    Cx = invM(Ax)
    Rp = identM(Ap)
    Mx = Cx
    Mp = convert(P, Mx)

    for i = 1:k+5
@show i
        Tp = Rp*Rp
        Rp = QuadLift(Ap, Mp, Tp, iX)      
            if iszeroM(Rp)
                return true
               #else
            #continue
            end
        Rx = convert(X, Rp)
        Tx = Rx*Rx
        Mx = Cx*Tx
@show        Mp = convert(P, Mx)
       
    end
    return false
end


#TODO check
# Integrality test of  D*inv(A) 
function UniCert(A::Generic.Mat{nf_elem}, D::Generic.Mat{nf_elem}, u::Int64)
n = nrows(A)
K = Hecke.base_ring(A)
zk= lll(maximal_order(K))
c1,c2=norm_change_const(zk)
d = degree(K)
p0 = fmpz(500)#p_start_mat(A) #fmpz(100) 
PB, XB = PXbounds(A, u)
P, np = genPrimes(p0, PB)
X, nx = genPrimes(P[np], XB)
@show P = RNS(P)
@show X = RNS(X)
k = nLifts(A, X.N, u)

    iX = Array(ZZ,np)
    for i = 1 : np
       iX[i] = invmod(X.N, P.p[i])  
    end
    Ap = RNSmat(P, A)
    Ax = RNSmat(X, A)
    Cx = invM(Ax)
    Rp = identM(Ap)
    Mx = Cx
    Mp = convert(P, Mx)

    Dp = RNSmat(P, D)
    Dx = RNSmat(X, D)
    Pp = Dp
    Nx = Dx*Cx
    Np = convert(P, Nx)    

    for i = 1:k+5
@show i
        Tp = Rp*Rp
        Rp = QuadLift(Ap, Mp, Tp, iX) 
        Up = Rp*Pp
        Pp = QuadLift(Np, Ap, Up, iX)     
            if iszeroM(Pp)
                return true
            end
        Rx = convert(X, Rp)
        Tx = Rx*Rx
        Mx = Cx*Tx
@show        Mp = convert(P, Mx)

        Px = convert(X, Pp)
        Ux = Rx*Px
        Nx = Ux*Cx
@show        Np = convert(P, Nx)
       
    end
    return false

end



#TODO
#
# convertMx to Mp is neq invmod(A,p), but work proof ??
# for n=300 sqrt doesn't work 
# Integer problem
# "@show" in double plus one can't be removed
# re-calculate bounds
# no method matching ^(::fmpz, ::fmpq)

# A=bad_mat(k,300,-1000:1000);
# @time UniCertNF(A, 100000)
# convert(fmpz, NaN)



#= example
include("/home/ajantha/Documents/RNS/UniCertNF.jl")
A=bad_mat(k,50,-1000:1000);
@time UniCertNF(A, 100000)

I=identity_matrix(A)
UniCert(A,I,100000)

=# 
