import Hecke: valuation, divexact, parent_type, elem_type, mul!, addeq!, parent
import Base: +, -, *, ^
export RNSnf_elem

function RandUpperMatZ(n::Int, U)
  m = identity_matrix(ZZ, n)
  for i=1:n
    for j=i+1:n
      m[i,j] = rand(ZZ, U)
    end
  end
  return m
end


function modinvM(A::fmpz_mat, X::fmpz)
  B0 = map_entries(lift, inv(map_entries(quo(ZZ, X)[1], A)))
  mod_sym!(B0, X)
  return B0
end

function my_mod_sym!(A::fmpz_mat, X::fmpz, ::Any)
  mod_sym!(A, X)
end


mutable struct RRS <: Hecke.Ring
  p::Array{fmpz, 1}
  P::Array{fmpz, 1}
  Pi::Array{fmpz, 1}
  r::fmpz
  N::fmpz
  ce

  function RRS(p::Array{fmpz, 1})
    s = new()
    s.p = p
    P = prod(p)
    s.P = [divexact(P, x) for x = p]
    s.Pi = [invmod(s.P[i], s.p[i]) for i=1:length(p)]
    s.r = next_prime(2^50)
    s.N = P
    s.ce = Hecke.crt_env(p)
    return s
  end

  function RRS(p::Array{<:Integer, 1})
    return RRS(fmpz[x for x = p])
  end

  function RRS(p::Array{<:Any, 1})
    return RRS(fmpz[x for x = p])
  end
end
function Base.show(io::IO, R::RRS)
  print(io::IO, "crt ring with moduli ", R.p)
end



mutable struct RRSelem <: Hecke.RingElem
  x::Array{fmpz, 1}
  r::fmpz
  R::RRS
  function RRSelem(X::RRS, a::fmpz)
    s = new()
    s.x = [mod(a, p) for p = X.p]
    s.r = mod(a, X.r)
    s.R = X
    return s
  end
  function RRSelem(X::RRS, a::Integer)
    return RRSelem(X, fmpz(a))
  end
  function RRSelem(X::RRS, a::Array{fmpz, 1}, k::fmpz)
    r = new()
    r.R = X
    r.x = a
    r.r = k
    return r
  end
end



function Base.show(io::IO, a::RRSelem)
  print(io, "crt: ", a.x)
end

elem_type(::RRS) = RRSelem
parent_type(::RRSelem) = RRS
parent_type(::Type{RRSelem}) = RRS

parent(a::RRSelem) = a.R

-(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]-b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r-b.r, a.R.r))
+(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]+b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r+b.r, a.R.r))
*(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]*b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r*b.r, a.R.r))
*(a::Integer, b::RRSelem) = RRSelem(b.R, [mod(a*b.x[i], b.R.p[i]) for i=1:length(b.x)], mod(a*b.r, b.R.r))
divexact(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]*invmod(b.x[i], a.R.p[i]), a.R.p[i]) for i=1:length(a.x)], mod(a.r*invmod(b.r, a.R.r), a.R.r))
-(a::RRSelem) = RRSelem(a.R, [mod(-a.x[i], a.R.p[i]) for i=1:length(a.x)], -a.r)
^(a::RRSelem, e::Integer) = RRSelem(a.R, [powmod(a.x[i], e, a.R.p[i]) for i=1:length(a.x)], powmod(a.r, e, a.R.r))
(R::RRS)() = RRSelem(R, fmpz[0 for i=1:length(R.p)], fmpz(0))
(R::RRS)(a::Integer) = RRSelem(R, a)
(R::RRS)(a::RRSelem) = a

function addeq!(a::RRSelem, b::RRSelem)
  for i=1:length(a.x)
    a.x[i] = mod(a.x[i] + b.x[i], a.R.p[i])
    a.r    = mod(a.r    + b.r   , a.R.r)
  end
  return a
end

function mul!(a::RRSelem, b::RRSelem, c::RRSelem)
  for i=1:length(a.x)
    a.x[i] = mod(b.x[i] * c.x[i], a.R.p[i])
    a.r    = mod(b.r    * c.r   , a.R.r)
  end
  return a
end

function check(a::RRSelem)
  z = fmpz(a)
  @assert mod(z, a.R.r) == a.r
end

#given x mod p_i and p_r, find x mod p
function extend(R::RRS, a::RRSelem, p::fmpz)
  k = sum(((a.x[i]*R.Pi[i]) % R.p[i]) * (R.P[i] % R.r) for i=1:length(R.p)) - a.r
  k = (k*invmod(R.N, R.r)) % R.r
  @assert k <= length(R.p)
  return (sum(((a.x[i]*R.Pi[i]) % R.p[i]) * (R.P[i] % p) for i=1:length(R.p)) - k*(R.N % p))%p
end


#########################################
#
#               RNS for fmpz_mat
#
#########################################
mutable struct RRSmat <: Hecke.RingElem
  x::Array{fmpz_mat,1}
  r::fmpz_mat 
  R::RRS
  function RRSmat(X::RRS, a::fmpz_mat)
    s = new()
    s.x = [Hecke.mod_sym(a, p) for p = X.p]
    s.r = Hecke.mod_sym(a, X.r)
    s.R = X
    return s
  end

  function RRSmat(X::RRS, a::Array{fmpz_mat,1}, k::fmpz_mat)
    r = new()
    r.R = X
    r.x = a
    r.r = k
    return r
  end

end


function Base.show(io::IO, a::RRSmat)
  print(io, "crt: ", a.x)
end

elem_type(::RRS) = RRSmat
parent_type(::RRSmat) = RRS
parent_type(::Type{RRSmat}) = RRS

parent(a::RRSmat) = a.R 

-(a::RRSmat, b::RRSmat) = RRSmat(a.R, [Hecke.mod_sym(a.x[i]-b.x[i], a.R.p[i]) for i=1:length(a.x)], Hecke.mod_sym(a.r-b.r, a.R.r))
+(a::RRSmat, b::RRSmat) = RRSmat(a.R, [Hecke.mod_sym(a.x[i]+b.x[i], a.R.p[i]) for i=1:length(a.x)], Hecke.mod_sym(a.r+b.r, a.R.r))
*(a::RRSmat, b::RRSmat) = RRSmat(a.R, [Hecke.mod_sym(a.x[i]*b.x[i], a.R.p[i]) for i=1:length(a.x)], Hecke.mod_sym(a.r*b.r, a.R.r))
invM(a::RRSmat) = RRSmat(a.R, [modinvM(a.x[i],a.R.p[i]) for i=1:length(a.x)], modinvM(a.r, a.R.r))
*(a::Integer, b::RRSmat) = RRSmat(b.R, [Hecke.mod_sym(a*b.x[i], b.R.p[i]) for i=1:length(b.x)], Hecke.mod_sym(a*b.r, b.R.r))
-(a::RRSmat) = RRSmat(a.R, [Hecke.mod_sym(-a.x[i], a.R.p[i]) for i=1:length(a.x)], Hecke.mod_sym(-a.r, b.R.r))
divexact(a::RRSmat, b::fmpz) = RRSmat(a.R, [Hecke.mod_sym(a.x[i]*invmod(b, a.R.p[i]), a.R.p[i]) for i=1:length(a.x)], Hecke.mod_sym(a.r*invmod(b, a.R.r), a.R.r))

# converter base of "a": a.R to B
convert(B::RRS, a::RRSmat) = RRSmat(B, [extend(a.R , a , B.p[i]) for i = 1: length(B.p)], a.r )
#TODO check?
QuadLift( A::RRSmat, M::RRSmat, T::RRSmat, iX :: Array{fmpz,1}, iXr :: fmpz) = RRSmat(A.R, [Hecke.mod_sym(iX[i]*(T.x[i]-A.x[i]*M.x[i]), A.R.p[i]) for i=1:length(A.x)], Hecke.mod_sym(iXr*(T.r - A.r*M.r), A.R.r))

mult(a::RRSmat, b::RRSmat) = RRSmat(a.R, [(a.x[i]*b.x[i]) for i=1:length(a.x)], a.r*b.r)

identM(a::RRSmat) = RRSmat(a.R, [identity_matrix(a.x[i]) for i=1:length(a.x)], identity_matrix(a.r))
zeroM(a::RRSmat) = RRSmat(a.R, [similar(a.x[i]) for i=1:length(a.x)], similar(a.r))

function iszeroM(a::RRSmat)
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

# extend for symmetric residue
function extend(R::RRS, a::RRSmat, p::fmpz)
  k = sum((Hecke.mod_sym(a.x[i]*R.Pi[i] , R.p[i])) *Hecke.mod_sym(R.P[i] , R.r) for i=1:length(R.p)) - a.r
  k =Hecke.mod_sym(k* Hecke.mod_sym(invmod(R.N, R.r),R.r), R.r)
#  @assert k <= length(R.p)
  return Hecke.mod_sym((sum(Hecke.mod_sym((a.x[i]*R.Pi[i]), R.p[i]) * Hecke.mod_sym(R.P[i], p) for i=1:length(R.p)) - k*Hecke.mod_sym(R.N , p)),p)
end



function extendOne(R::RRS, a::RRSmat, p::fmpz)
  k = sum((mod(a.x[i]*R.Pi[i] , R.p[i])) * mod(R.P[i] , R.r) for i=1:length(R.p)) - a.r
  k = mod(k*invmod(R.N, R.r), R.r)
#  @assert k <= length(R.p)
  return mod((sum(mod((a.x[i]*R.Pi[i]), R.p[i]) * mod(R.P[i], p) for i=1:length(R.p)) - k*mod(R.N , p)),p)
end




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
        start = previous_prime(start)
        push!(a, start)
        tot *= start
    end
        return a, i
end


#TODO chage as C-code simple way
function p_start_mat(A:: fmpz_mat)
    n = nrows(A)
    return numerator(floor(fmpz(floor(sqrt(4*n*(2^53-1)+1) +(2*n-1)))//(2*n)))
end

# bound for basis P and X 
function PXbounds(A:: fmpz_mat)
    n = nrows(A)
    S = maximum(A)
   return   fmpz(round(1.2002*n*S)), fmpz(round(3.61*n^2*S))
end



# number of lifting operations in UniCert
function nLifts(A:: fmpz_mat, X:: fmpz)
    n = nrows(A)
    if isodd(n)
        n = n+1
    end
    S = maximum(A)
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



function UniCertZ(A::fmpz_mat)
n = nrows(A)
p0 = p_start_mat(A)
PB, XB = PXbounds(A)
P, np = genPrimes(p0, PB)
# C -code use np-1
X, nx = genPrimes(P[np], XB)
P = RRS(P)
X = RRS(X)
k = nLifts(A, X.N)

    iX = Array(ZZ,np)
    for i = 1 : np
       iX[i] = invmod(X.N, P.p[i])  
    end
     iXr = invmod(X.N, X.r)


    Ap = RRSmat(P, A)
    Ax = RRSmat(X, A)
#TODO C-code check existence
    Cx = invM(Ax)
    Rp = identM(Ap)
    Mx = Cx
    Mp = convert(P, Mx)

    for i = 1:k
 @show  Tp = Rp*Rp
 #      Tp = mult(Rp,Rp)
 @show  Rp = QuadLift(Ap, Mp, Tp, iX, iXr)

            if iszeroM(Rp)
                return true
            else
                continue
            end

 @show  Rx = convert(X, Rp)
        Tx = Rx*Rx
 #      Tx = mult(Rx, Rx)
        Mx = Cx*Tx
        Mp = convert(P, Mx)        
    end
            return false

end



#= example
include("/home/ajantha/Documents/RNS/UniCertRNS.jl")

A=RandUpperMatZ(6,1000:(100^4));
UniCertZ(A)

=#



