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



###################################################################
#
#            Residue Number System
#
###################################################################

function array_mat(A::MatElem{T}) where T #(A::Generic.Mat{nf_elem})
   a = []
    for i=1:nrows(A)
        for j=1:ncols(A)
        push!(a, A[i,j])
        end
    end
    return a
end


mutable struct RNS <: Hecke.Ring
  p::Array{fmpz, 1}
  P::Array{fmpz, 1}
  Pi::Array{fmpz, 1}
  w::Array{fmpq, 1}
  c::Array{fmpz, 1} 
  F::Array{Tuple{FqFiniteField,Hecke.NfOrdToFqMor}, 1} 
#  r::fmpz
  N::fmpz
  ce
  O:: NfAbsOrd{AnticNumberField,nf_elem}

  function RNS(zk::NfAbsOrd{AnticNumberField,nf_elem} , p::Array{fmpz, 1})
    s = new()
    s.O = zk
    s.p = p
    P = prod(p)
    s.P = [divexact(P, x) for x = p]
    s.Pi = [invmod(s.P[i], s.p[i]) for i = 1:length(p)]
#    s.r = next_prime(2^50)
    s.N = P
    s.ce = Hecke.crt_env(p)
    s.w = [s.Pi[i]//s.p[i] for i = 1:length(p)]
    s.c = [s.P[i]*s.Pi[i] for i = 1:length(p)]
    s.F = [ResidueField(zk,prime_decomposition(zk,s.p[i])[1][1]) for i = 1:length(p) ]
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


###################################################################
#
#            RNS for matrices over number fields
#
###################################################################

function imageM(mF::Hecke.NfOrdToFqMor, A::Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}})
a = zero_matrix(codomain(mF), nrows(A), ncols(A))
   for i=1:nrows(A)
     for j=1:ncols(A)
	    a[i,j]= mF(A[i,j])
     end
   end
return a
end


function preimageM(mF::Hecke.NfOrdToFqMor, A::fq_mat)
a = zero_matrix(domain(mF), nrows(A), ncols(A))
   for i=1:nrows(A)
     for j=1:ncols(A)
	    a[i,j]= preimage( mF, A[i,j])
     end
   end
return a
end





mutable struct RNSmat <: Hecke.RingElem
  x::Array{fq_mat,1}
#  r::fmpz_mat 
  R::RNS
  function RNSmat(X::RNS, a::Generic.MatSpaceElem{nf_elem})
    s = new()
#    s.x = [mod(a, p) for p = X.p]
     s.x = [matrix(F[1],nrows(a),ncols(a),[F[2](X.O(x)) for x in array_mat(a)]) for F=X.F]
#    s.x = [imageM(F[2], a) for F=X.F]
#    s.r = Hecke.mod_sym(a, X.r)
    s.R = X
    return s
  end

  function RNSmat(X::RNS, a::Array{fq_mat,1})
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

-(a::RNSmat, b::RNSmat) = RNSmat(a.R, [a.x[i]-b.x[i] for i=1:length(a.x)])

+(a::RNSmat, b::RNSmat) = RNSmat(a.R, [a.x[i]+b.x[i] for i=1:length(a.x)])

*(a::RNSmat, b::RNSmat) = RNSmat(a.R, [a.x[i]*b.x[i] for i=1:length(a.x)])

invM(a::RNSmat) = RNSmat(a.R, [inv(a.x[i]) for i=1:length(a.x)])

-(a::RNSmat) = RNSmat(a.R, [-a.x[i] for i=1:length(a.x)])

#QuadLift( A::RNSmat, M::RNSmat, T::RNSmat, iX :: Array{fmpz,1}) = RNSmat(A.R, [iX[i]*(T.x[i]-A.x[i]*M.x[i]) for i=1:length(A.x)])
QuadLift( A::RNSmat, M::RNSmat, T::RNSmat, iX :: Array{Any,1}) = RNSmat(A.R, [iX[i]*(T.x[i]-A.x[i]*M.x[i]) for i=1:length(A.x)])

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



############################################
#       convert: Using CRT
############################################


function crt_recon(A::NfOrdIdl, a::NfOrdElem, B::NfOrdIdl, b::NfOrdElem )
zk = parent(a)     
v,u=idempotents(A,B)   
de=  a*u+b*v
D = A*B
T1 = lll(basis_matrix(D))
U = matrix(FlintQQ,degree(zk),degree(zk),array_mat(T1))
TT = coordinates(de)
V =matrix(FlintQQ,degree(zk),1,TT)
W = Hecke.solve(U',V)
F = []
k=0
    for i=1:nrows(T1)
        push!(F, order(D)([T1[i,j] for j=1:ncols(T1)]))
    end

    for j=1:degree(zk)
        k += F[j]*(round(BigInt, Rational{BigInt}(W[j,1])))
    end
    return de= de-k
end


function crt_recon_mat(A::NfOrdIdl, a::Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}}, B::NfOrdIdl, b::Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}} )
zk = base_ring(a)
C=zero_matrix(zk,nrows(a),ncols(a))

    for i=1:nrows(a)
        for j=1:ncols(a)
             C[i,j] = crt_recon(A, a[i,j], B,b[i,j])
        end
    end
return C
end


function crt_RNSmat(a::RNSmat)
R = a.R
x = [preimageM(R.F[i][2],a.x[i]) for i=1:length(a.x)]
zk = base_ring(x[1])
D = prime_decomposition(zk,R.p[1])[1][1]
I = x[1]
    for i = 2:length(x)
        lp = prime_decomposition(zk,R.p[i])[1][1]   
        I = crt_recon_mat(D, I, lp, x[i])
        D = D*lp
    end
   return I
end

convert(B::RNS, a::RNSmat) = RNSmat(B, [imageM(B.F[i][2], crt_RNSmat(a)) for i=1:length(B.p)] )



#given x mod p_i and p_r, find x mod p
#TODO Not Work for ResidueFiels
############################################
#       convert: Mixed radix base extension
############################################

function mixed_radix(R::RNS, a::RNSmat)#, li::Int = typemax(Int))
A = Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}}[]
    for i=1:length(a.x)
        y = a.x[i]
        for j=1:i-1
            #y = invmod(R.p[j], R.p[i])*(y-imageM(R.F[i][2], A[j]))
            y = inv(R.F[i][2](zk(R.p[j])))*(y-imageM(R.F[i][2], A[j]))
        end
        push!(A, preimageM(R.F[i][2],y))
      #  push!(A, y)
    end
    return A
  #so a = A[1] + A[2]*p[1] + A[3]*p[1]*p[2] ...s
end

function rss_mat_from_radix(R::RNS,  x::Array{Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}},1})
z = Generic.MatSpaceElem{NfAbsOrdElem{AnticNumberField,nf_elem}}[]
q = fmpz(1)
    for i=1:length(R.p)
        push!(z, q*x[i])
        q *=R.p[i]
    end
   return z
end


function extend_mix(B::RNS, a::RNSmat)
z = fq_mat[]
LL = mixed_radix(a.R, a)
L = rss_mat_from_radix(a.R, LL)
    for i = 1: length(B.p)
#        push!(z, modsM(sum(modsM(L[j],B.p[i]) for j = 1:length(L)), B.p[i]))
        push!(z,  (sum(imageM(B.F[i][2], L[j]) for j = 1:length(L))))

    end 
    return z
end 


# converter base of "a": a.R to B
# convert(B::RNS, a::RNSmat) = RNSmat(B, extend_mix(B, a) )
#TODO while using mixed radix convert, weight w and c can be removed from the RNS

#TODO Not Work for ResidueFiels
#############################################
#       convert: Approximated base extension
#############################################

function mat_mul_fq(K:: AnticNumberField, A::MatElem{T}, p::fmpq) where T
#   K = Hecke.base_ring(A)   Find base ring, given maximal order
   a = zero_matrix(K, nrows(A), ncols(A))
   for i=1:nrows(A)
     for j=1:ncols(A)
	    a[i,j] = p*K(A[i,j])
     end
   end
   return a
end


function round_coeff(A::Generic.MatSpaceElem{nf_elem}, O::NfAbsOrd{AnticNumberField,nf_elem} )
 K = Hecke.base_ring(A) 
 d = degree(K)
 S = zero_matrix(ZZ,1,d)
 a = zero_matrix(O, nrows(A), ncols(A))
   for i= 1: nrows(A)   
        for j= 1:ncols(A)
            l = coeffs(A[i,j])
            for k = 1:d
                S[1,k] = fmpz(round(l[k]))
            end
	        a[i,j]= O(Hecke.elem_from_mat_row(K,S,1,fmpz(1))) 
        end
   end
   return a
end

# extend for symmetric residue
function extend_round(K::AnticNumberField, B::RNS, a::RNSmat )
    R = a.R
    corr = round_coeff(sum(mat_mul_fq(K, preimageM(R.F[i][2],a.x[i]), R.w[i]) for i=1:length(R.p)), B.O)         
  # k = -Hecke.mod_sym(R.N, p)
    ap = sum(R.c[i]*preimageM(R.F[i][2],a.x[i]) for i=1:length(R.p))
    aB = [imageM(B.F[j][2], ap-(Hecke.mod_sym(R.N, B.p[j]))*corr) for j=1:length(B.p)]
    return aB 
end


# converter base of "a": a.R to B 
# convert(B::RNS, a::RNSmat) = RNSmat(B, extend_round(nf(B.O), B, a))
#TODO while using approximation based convert, add weight w and c to the RNS




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
function p_start_mat(A:: Generic.Mat{nf_elem})
    n = fmpz(nrows(A))
    return numerator(floor(fmpz(floor(root(4*n*(2^53-1)+1, 2) +(2*n-1)))//(2*n)))
end

# bound for basis P and X 
function PXbounds(A:: Generic.Mat{nf_elem}, S::Int64)
n = nrows(A)
K = Hecke.base_ring(A)
zk= lll(maximal_order(K))
c1,c2 = norm_change_const(zk)
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
    bound = fmpz(n)^(div(n, 2)-2)*fmpz(S)^(n-2)
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
p0 = fmpz(1000)# p_start_mat(A) #fmpz(100) 
@show PB, XB = PXbounds(A, u)
println("prime gen")
@time begin
@show P, np = genPrimes(p0, PB)# [fmpz(1013), fmpz(1009),fmpz(997), fmpz(991), fmpz(983)], 5#
@show X, nx = genPrimes(P[np], XB)
end
 P = RNS(zk, P)
 X = RNS(zk, X)
k = nLifts(A, X.N, u)

    
    iX=[]
    for i = 1 : np
        push!(iX, inv(P.F[i][2](zk(X.N))) )  
    end
        Ap = RNSmat(P, A)
        Ax = RNSmat(X, A)
#TODO C-code check existence
println("inv")
@time   Cx = invM(Ax)
        Rp = identM(Ap)
        Mx = Cx
println("convert")
@show   Mp = convert(P, Mx)

    for i = 1:k+5
@show i
println("T-mult")
            Tp = Rp*Rp
println("Double_lift")

@show       Rp = QuadLift(Ap, Mp, Tp, iX)      
            if iszeroM(Rp)
                return true
            end
println("convert 1")
        Rx = convert(X, Rp)
println("mult")
        Tx = Rx*Rx
        Mx = Cx*Tx
println("convert 2")
        Mp = convert(P, Mx)

    end
    return false

end



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
@show P = RNS(zk,P)
@show X = RNS(zk,X)
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
        Up = Rp*Pp
        Rp = QuadLift(Ap, Mp, Tp, iX) 
        Pp = QuadLift(Np, Ap, Up, iX)     
            if iszeroM(Pp)
                return true
            end
        Rx = convert(X, Rp)
        Tx = Rx*Rx
        Mx = Cx*Tx
        Mp = convert(P, Mx)

        Px = convert(X, Pp)
        Ux = Rx*Px
        Nx = Ux*Cx
        Np = convert(P, Nx)
    end
    return false

end



#= example
Zx,x=FlintZZ["x"]
k,a=number_field(x^3+7x+1)
A=matrix(k,3,3,[-71*a^2 + 12*a - 91,  -14464*a^2 + 22982*a - 4279,  40281*a^2 - 11436*a + 2503, 1, -21*a^2 + 53*a + 92, 0,0,1,96*a^2 + 95*a + 88])
include("/home/ajantha/Documents/RNS/UniCertCRT.jl")
UniCertNF(A, 10000000000)


=# 
