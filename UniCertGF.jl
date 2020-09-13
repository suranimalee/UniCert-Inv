import Hecke: divexact, parent_type, elem_type, mul!, addeq!, parent
import Base: +, -, *, ^

###################################################################
#
#            Modular environment for totally split primes
#
###################################################################


mutable struct modular_Genv
  p::fmpz
  up::UInt
  upinv::UInt

  fld::Array{Hecke.GaloisField, 1}
  fldx::Array{GFPPolyRing, 1}
  ce::crt_env{gfp_poly}
  rp::Array{gfp_poly, 1}
  res::Array{Hecke.gfp_elem, 1}
  Fpx::GFPPolyRing
  K::AnticNumberField
  Rp::Array{gfp_poly, 1}
  F::Array{Hecke.NfToGFMor_easy, 1}  


  function modular_Genv()
    return new()
  end
end

Base.isempty(me::modular_Genv) = !isdefined(me, :ce)

function show(io::IO, me::modular_Genv)
  if isempty(me)
    println("modular environment for p=$(me.p), using $(0) ideals")
  else
    println("modular environment for p=$(me.p), using $(me.ce.n) ideals")
  end
end


#  modular_Ginit(K::AnticNumberField, p::fmpz) -> modular_Genv
#  modular_Ginit(K::AnticNumberField, p::Integer) -> modular_Genv

#  Given a number field $K$ and an ``easy'' totally split prime $p$ (ie. fits into an \code{Int} and is coprime to the polynomial discriminant), compute the Galois fields of the associated primes ideals above $p$. Returns data that can be used by \code{modular_Gproj} and \code{modular_Glift}.

function modular_Ginit(K::AnticNumberField, p::fmpz; deg_limit::Int=0, max_split::Int = 0)
  @hassert :NfOrd 1 isprime(p)
  zk = maximal_order(k)
  me = modular_Genv()
  G =  GF(Int(p)) 
  me.Fpx = PolynomialRing( GF(Int(p) , cached = false), "_x", cached=false)[1]  
  fp = me.Fpx(K.pol)
  lp = factor(fp)
  if Set(values(lp.fac)) != Set([1])
    throw(BadPrime(p))
  end
  pols = collect(keys(lp.fac))

  me.ce = crt_env(pols)
  Fm = [Hecke.NfOrdToGFMor(zk, G, x)  for x = pols]
  me.F = [Hecke.extend_easy(x, K)  for x = Fm]
  #TODO parent and codamain are different?? 
  l = K()
  #me.fld = [codomain(x) for x=Fm]
  me.fld = [parent(x(l)) for x=me.F]
  me.rp = Vector{gfp_poly}(undef, length(pols))
  me.res = Vector{Hecke.gfp_elem}(undef, me.ce.n)

  me.p = p
  me.K = K
  me.up = UInt(p)
  me.upinv = ccall((:n_preinvert_limb, Hecke.libflint), UInt, (UInt, ), me.up)
  return me
end

function modular_Ginit(K::AnticNumberField, p::Integer; deg_limit::Int=0, max_split::Int = 0)
  return modular_Ginit(K, fmpz(p), deg_limit = deg_limit, max_split = max_split)
end


# modular_Gproj(a::nf_elem, me::modular_Genv) -> Array{Hecke.gfp_elem, 1} 
# Given an algebraic number $a$ and data \code{me} as computed by \code{modular_Ginit}, project $a$ onto the residue class fields.

function modular_Gproj(a::nf_elem, me::modular_Genv)
  for i=1:me.ce.n
    me.res[i] = me.F[i](a)
  end
  return me.res
end


# modular_Glift(a::Array{Hecke.gfp_elem}, me::modular_Genv) -> nf_elem 
# Given an array of elements as computed by \code{modular_Gproj}, compute a global pre-image using some efficient CRT.
# TODO Hecke crash by the second ccall
function modular_Glift(a::Array{Hecke.gfp_elem, 1}, me::modular_Genv)
  for i=1:me.ce.n
    #  ccall((:nmod_poly_set, Hecke.libflint), Nothing, (Ref{gfp_poly}, Ref{Hecke.gfp_elem}), me.rp[i], a[i])
    me.rp[i]=me.Fpx(a[i])
  end

  ap = crt(me.rp, me.ce)
  r = me.K()
  for i=0:ap.length-1
    u = lift(coeff(ap, i))
    # u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{nmod_poly}, Int), ap, i)
    # u = ccall((:Hecke.nmod_poly_get_coeff_ui, Hecke.libflint), UInt, (Ref{gfp_poly}, Int), ap, i)
    Hecke._num_setcoeff!(r, i, u)
  end
  return r
end


#  modular_Gproj(a::Generic.Mat{nf_elem}, me::modular_Genv) -> Array{Matrix}
#  modular_Gproj(a::Generic.Mat{NfOrdElem}, me::modular_Genv) -> Array{Matrix}
#  Apply the \code{modular_Gproj} function to each entry of $a$. Computes an array of matrices over the respective residue class fields.

function modular_Gproj(a::Generic.Mat{nf_elem}, me::modular_Genv)
  Mp = Hecke.gfp_mat[]
  for i=1:me.ce.n
    push!(Mp, zero_matrix(me.fld[i], nrows(a), ncols(a)))
  end
  for i=1:nrows(a)
    for j=1:ncols(a)
        im =modular_Gproj(a[i,j], me)
      for k=1:me.ce.n
        Hecke.setindex!(Mp[k], Hecke.deepcopy(im[k]), i, j)
      end
    end
  end  
  return Mp
end  



# modular_Glift(ap::Array{gfp_poly, 1}, me::modular_Genv) -> Array
# Given an array of matrices as computed by \code{modular_Gproj}, compute a global pre-image using some efficient CRT.

function modular_Glift(ap::Array{Hecke.gfp_mat, 1}, me::modular_Genv)
  A = zero_matrix(me.K, nrows(ap[1]), ncols(ap[1]))
  for i=1:nrows(A)
    for j=1:ncols(A)
      A[i,j] = modular_Glift([ap[k][i,j] for k=1:length(ap)], me)
    end
  end
  return A
end




###################################################################
#
#             Tools for unimodular certification
#         #########################################
###################################################################


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


# Apply the \code{Hecke.mod_sym} function to each entry of $A$. 
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


function array_mat(A::MatElem{T}) where T
  a = []
    for i=1:nrows(A)
      for j=1:ncols(A)
        push!(a, A[i,j])
      end
  end
  return a
end


function invmod_back(p::Array{fmpz, 1}) 
  a = []
    for i=1:length(p)
      b = []
      for j=1:i-1
        push!(b, invmod(p[j], p[i]))
      end
    push!(a, b)
  end
  return a
end

###################################################################
#
#                Residue Number System
#
###################################################################

mutable struct RNS <: Hecke.Ring
  p::Array{fmpz, 1}
  P::Array{fmpz, 1}
  Pi::Array{fmpz, 1}
  ip
  w::Array{fmpq, 1}
  c::Array{fmpz, 1} 
  N::fmpz
  me ::Array{modular_Genv, 1}
  O:: NfAbsOrd{AnticNumberField,nf_elem}
  #ce

  function RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , p::Array{fmpz, 1})
    s = new()
    s.O = zk
    s.p = p
    P = prod(p)
    s.P = [divexact(P, x) for x = p]
    s.Pi = [invmod(s.P[i], s.p[i]) for i = 1:length(p)]
    s.ip = invmod_back(p)
    s.me = [modular_Ginit(nf(zk), s.p[i]) for i = 1:length(p)]
    s.N = P
    s.w = [s.Pi[i]//s.p[i] for i = 1:length(p)]
    s.c = [s.P[i]*s.Pi[i] for i = 1:length(p)]
    #s.ce = Hecke.crt_env(p)
    return s
  end

  function RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , p::Array{<:Integer, 1})
    return RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , fmpz[x for x = p])
  end

  function RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , p::Array{<:Any, 1})
    return RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , fmpz[x for x = p])
  end
end
function Base.show(io::IO, R::RNS)
  print(io::IO, "crt ring with moduli ", R.p)
end



###################################################################
#
#            RNS for matrices over number fields
#
###################################################################

mutable struct RNSmat <: Hecke.RingElem
  R::RNS
  m

  function RNSmat(X::RNS, a::Generic.MatSpaceElem{nf_elem})
    s = new()
    s.m = [modular_Gproj(a, Me) for Me = X.me]
    s.R = X
    return s
  end

  function RNSmat(X::RNS, c::Array{Array{gfp_mat,1},1})
    r = new()
    r.R = X
    r.m = c
    return r
  end

  function RNSmat(X::RNS, c::Array{Any,1})
    r = new()
    r.R = X
    r.m = c
    return r
  end
end


function Base.show(io::IO, a::RNSmat)
    print(io, "crt: ",  a.m)
end

elem_type(::RNS) = RNSmat
parent_type(::RNSmat) = RNS
parent_type(::Type{RNSmat}) = RNS

parent(a::RNSmat) = a.R 

-(a::RNSmat, b::RNSmat) = RNSmat(a.R, [a.m[i]-b.m[i] for i=1:length(a.m)] )

+(a::RNSmat, b::RNSmat) = RNSmat(a.R, [a.m[i]+b.m[i] for i=1:length(a.y)])

*(a::RNSmat, b::RNSmat) = RNSmat(a.R, [[a.m[i][j]*b.m[i][j] for j = 1:length(a.m[i])] for i=1:length(a.m)])

invM(a::RNSmat) = RNSmat(a.R, [[inv(a.m[i][j]) for j = 1:length(a.m[i])] for i=1:length(a.m)])

-(a::RNSmat) = RNSmat(a.R, [-a.m[i] for i=1:length(a.m)])

QuadLift( A::RNSmat, M::RNSmat, T::RNSmat, iX :: Array{fmpz,1}) = RNSmat(A.R, [[iX[i]*(T.m[i][j]-A.m[i][j]*M.m[i][j]) for j = 1:length(A.m[i])] for i=1:length(A.m)])

identM(a::RNSmat) = RNSmat(a.R, [[identity_matrix(a.m[i][j]) for j = 1:length(a.m[i])] for i=1:length(a.m)])
zeroM(a::RNSmat) = RNSmat(a.R,  [[similar(a.m[i][j]) for j = 1:length(a.m[i])] for i=1:length(a.m)])

function iszeroM(a::RNSmat)
i = 1
  while true
    fl = iszero(a.m[i])
    if   !fl
      return false
    end
    if i == length(a.m)
      return true
    end
      i += 1        
  end
end

############################################
#       convert: Mixed radix base extension
############################################

function ExtendEnv(B::RNS, a::RNSmat) 
A = Generic.MatSpaceElem{nf_elem}[]
R = a.R
  for i=1:length(a.m)
    push!(A, modular_Glift(a.m[i], R.me[i]))
  end
L = Generic.MatSpaceElem{nf_elem}[]
  for i=1:length(A)
    y = A[i]
    for j=1:i-1
        #y = modsM(((y-L[j])*invmod(R.p[j], R.p[i])), R.p[i])
        y = modsM(((y-L[j])*R.ip[i][j]), R.p[i])
    end
    push!(L, y)
  end
q = fmpz(1)
  for i=1:length(R.p)
    L[i] = q*L[i]
    q *=R.p[i]
  end
zz = []
  for i = 1: length(B.p)
    M = sum(modsM(L[j], B.p[i]) for j = 1:length(L))
    push!(zz, modular_Gproj(M, B.me[i]))
  end 
    return zz
end


# for this convert, weight w and c can be removed from RNS
 convert(B::RNS, a::RNSmat) = RNSmat(B,  ExtendEnv(B,a))


#############################################
#       convert: Approximated base extension
#############################################

function mat_mul_fq(A::MatElem{T}, p::fmpq) where T
  K = Hecke.base_ring(A)  
  a = zero_matrix(K, nrows(A), ncols(A))
  for i=1:nrows(A)
    for j=1:ncols(A)
      a[i,j] = p*A[i,j]
    end
  end
  return a
end


function round_coeff(A::Generic.MatSpaceElem{nf_elem})
  K = Hecke.base_ring(A) 
  d = degree(K)
  S = zero_matrix(ZZ,1,d)
  a = zero_matrix(K, nrows(A), ncols(A))
    for i= 1: nrows(A)   
      for j= 1:ncols(A)
        l = coeffs(A[i,j])
          for k = 1:d
            S[1,k] = fmpz(round(l[k]))
          end
            a[i,j]= Hecke.elem_from_mat_row(K,S,1,fmpz(1))
      end
    end
    return a
end


function extend_round(R::RNS, a::RNSmat, p::fmpz)
  A = Generic.MatSpaceElem{nf_elem}[]
    for i=1:length(a.m)
      push!(A, modular_Glift(a.m[i],R.me[i]))
    end
    corr =round_coeff(sum(mat_mul_fq(A[i], R.w[i]) for i=1:length(R.p)))         
    k = -Hecke.mod_sym(R.N, p)
    ap = sum(Hecke.mod_sym(R.c[i], p)*A[i] for i=1:length(R.p))  
    ap = modsM(ap+ k*corr, p)
    return ap 
end

# convert(B::RNS, a::RNSmat) = RNSmat(B, [modular_Gproj(extend_round(a.R , a , B.p[i]), B.me[i]) for i = 1: length(B.p)])



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



#TODO if prime_decomposition and type computation is expensive, pass the ideal to RNS
function genPrimesNext(start::Int64, bound::fmpz, O::NfAbsOrd{AnticNumberField,nf_elem})
  n = degree(O)
  tot = fmpz(1)
  a = []
  i = 0
  while tot < bound
    start = Hecke.next_prime(start)
    P = prime_decomposition_type(O,start)
    if length(P) == n
      i +=1
      push!(a, start)
      tot *= start
    end
  end
  return a, i
end


#TODO chage as C-code simple way
function p_start_mat(A:: Generic.Mat{nf_elem})
  n = fmpz(nrows(A))
  return numerator(floor(fmpz(floor(root(4*n*(2^53-1)+1, 2) +(2*n-1)))//(2*n)))
end

# bound for basis P and X 
function PXbounds(A:: Generic.Mat{nf_elem}, S::Int64, c1:: BigFloat, c2:: BigFloat)
  n = nrows(A)
  K = Hecke.base_ring(A)
  d = degree(K)
  n = nrows(A)
  return   fmpz(round(1.2002*n*c1*sqrt(c2)*d*S)), fmpz(round(3.61*c2*(n*c1*d)^2*S))
end


#TODO check bound
# number of lifting operations in UniCert
function nLifts(A:: Generic.Mat{nf_elem}, X:: fmpz, S:: Int64, c1:: BigFloat, c2:: BigFloat)
  n = nrows(A)
  K = Hecke.base_ring(A)
  d = degree(K)
  n = nrows(A)
  if isodd(n)
    n = n+1
  end
  c = fmpz(round(sqrt(c2)*c1^(div(n,2))))
  bound = c*fmpz(n)^(div(n, 2)-2)*fmpz(S)^(n-2)
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
# Given a matrix A with p_start:: a starting value to generate primes and u :: maximum coefficient size of matrix entries of A \code{UniCertNF} checkes whether A is unimodular

function UniCertNF(A::Generic.Mat{nf_elem},  p_start::Int64, u::Int64)
  n = nrows(A)
  K = Hecke.base_ring(A)
  zk= lll(maximal_order(K))
  c1,c2=norm_change_const(zk)
  d = degree(K)
  # p0 = p_start_mat(A) 
  PB, XB = PXbounds(A, u, c1, c2)
  println("prime gen")
#@show P, np = genPrimes(p0, PB)
#@show X, nx = genPrimes(P[np], XB)
@show X, nx = genPrimesNext(p_start, XB, zk)
@show P, np = genPrimesNext(X[nx], PB, zk)

  P = RNS(zk, P)
  X = RNS(zk, X)
@show  k = nLifts(A, X.N, u, c1, c2)

    iX = Array(ZZ,np)
    for i = 1 : np
      iX[i] = invmod(X.N, P.p[i])  
    end

        Ap = RNSmat(P, A)
        Ax = RNSmat(X, A)
#TODO As C-code check existence of inv 
println("inv")
@time   Cx = invM(Ax)
        Rp = identM(Ap)
        Mx = Cx
println("convert")
        Mp = convert(P, Mx)

        for i = 1 : k+3
@show i
@time     Tp = Rp*Rp
println("Double_lift")

          Rp = QuadLift(Ap, Mp, Tp, iX)      
            if iszeroM(Rp)  
              return true
            end
println("convert1")
@time       Rx = convert(X, Rp)
println("mult")
@time       Tx = Rx*Rx
@time       Mx = Cx*Tx
println("convert2")
@time       Mp = convert(P, Mx)

        end
      return false
end





############### Using totally split primes with prime fields
  

#= example
include("/home/ajantha/Documents/RNS/UniCertGF.jl")
Zx,x=FlintZZ["x"]
k,a=number_field(x^3+7x+1)
A=bad_mat(k,50,-100:100);
@time UniCertNF(A, 100, 10000)


UniCert(A:: matrix, p:: prime start, u:: bound on coefficients of A)
=# 
