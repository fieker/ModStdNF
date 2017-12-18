function to_singular(A::Array{Nemo.Generic.MPoly{Nemo.nf_elem}, 1}, gp)
  Rpt = parent(gp)
  R = base_ring(gp)
  p = Int(modulus(R))

  K = base_ring(A[1])
  Kx = parent(A[1])

  Rps = Singular.N_ZpField(p)
  Rpx = Singular.PolynomialRing(Rps, [ String(x) for x = Kx.S])[1]

  n = Kx.N
  exp = zeros(Cint, n+1)

  Res = elem_type(Rpx)[]

  for a = A
    res = C_NULL
    for j=1:a.length
      ap = Rpt(a.coeffs[j]) % gp
      if iszero(ap)
        continue
      end

      aS_ptr = Singular.libSingular.p_Init(Rpx.ptr)

      for i=1:n
        exp[i+1] = a.exps[i, j]
      end

      Singular.libSingular.p_SetExpV(aS_ptr, exp, Rpx.ptr)
      Singular.libSingular.pSetCoeff0(aS_ptr, Clong(lift(coeff(ap, 0))), Rpx.ptr)

      if res == C_NULL
        res = aS_ptr
      else 
        res = Singular.libSingular.p_Add_q(res, aS_ptr, Rpx.ptr)
      end
    end
    push!(Res, Rpx(res))
  end
  return Singular.Ideal(Rpx, Res)
end

function from_singular(a::Singular.sideal, Kx::MPolyRing{nf_elem})
  K = base_ring(Kx)

  Res = Nemo.Generic.MPoly{nf_elem}[]
  N = Kx.N
  for i=1:Singular.ngens(a)
    res = Kx()
    fit!(res, length(a[i]))
    j = 1
    for (c, e) in Singular.coeffs_expos(a[i])
      res.coeffs[j] = K(Int(c))
      for k=1:N
        res.exps[k, j] = e[k]
      end
      j += 1
    end
    res.length = j-1
    push!(Res, res)
  end
  return Res
end

function from_singular_crt(a::Singular.sideal, Res::Array{Nemo.Generic.MPoly{nf_elem}, 1}, pp::fmpz)
  Kx = parent(Res[1])
  K = base_ring(Kx)

  N = Kx.N
  p = fmpz(Singular.characteristic(parent(a[1])))

  for i=1:Singular.ngens(a)
    j = 1
    over = Kx(0)
    for (c, e) in Singular.coeffs_expos(a[i])
      if any(k -> e[k] != Res[i].exps[k, i], 1:N)
        if j==1
          error("unlucky prime (wrong leading coeff) found")
        end
        Res[i].coeffs[j] = Hecke.induce_crt(K(0), p, Res[i].coeffs[j], pp)[1]
        fit!(over, length(over)+1)
        l = length(over)+1 
        over.coeffs[l] = Hecke.induce_crt(K(Int(c)), p, K(0), pp)[1]
        for k=1:N
          over.exps[k, l] = e[k]
        end
        over.length += 1
      else  
        Res[i].coeffs[j] = Hecke.induce_crt(K(Int(c)), p, Res[i].coeffs[j], pp)[1]
      end
      j += 1
    end
    Res[i] += over
  end
  return Res
end

function reco_init(K::AnticNumberField, p::fmpz, f::fmpz_poly)
  M = MatrixSpace(FlintZZ, degree(K), degree(K))(1)
  M[1,1] = p
  t = gen(parent(f))
  q, r = divrem(gen(parent(f)),  f)
  for i=2:degree(K)
    M[i, 1] = -coeff(r, 0)
    q, r = divrem(r*t,  f)
  end
  M = Nemo.lll(M)
  Mi, d = Nemo.pseudo_inv(M)
  return (M, Mi, d)
end

function reco(data, f::nf_elem)
  M, Mi, d = data
  K = parent(f)
  N = matrix(FlintZZ, 1, degree(K), [ numerator(coeff(f, i)) for i=0:degree(parent(f))-1])
  x = N*Mi
  y = matrix(FlintZZ, 1, degree(K), [round(fmpq(x[1, i], d)) for i=1:degree(K)])*M
  b = basis(K)
  return f-sum(b[i]*y[1, i] for i=1:degree(K))
end

function reco_den_int(data, f::nf_elem)
  n = degree(parent(f))
  M = MatrixSpace(FlintZZ, n+1, n+1)()
  f = reco(data, f)
  Hecke._copy_matrix_into_matrix(M, 2, 2, data[1])
  M[1,1] = 1
  for i=1:n
    M[1, i+1] = numerator(coeff(f, i-1))
  end

  L = lll(M) #need destructive version!
  zero!(f)
  b = basis(parent(f))
  for i=1:n
    f += b[i]*L[1, i+1]
  end
  return f//L[1,1]
end

function reco_den_alg(data, f::nf_elem)
  n = degree(parent(f))
  M = MatrixSpace(FlintZZ, 2*n, 2*n)(1)
  f = reco(data, f)
  Hecke._copy_matrix_into_matrix(M, n+1, n+1, data[1])
  R = representation_mat(f)
  Hecke._copy_matrix_into_matrix(M, 1, n+1, R)
  L = lll(M) #need destructive version!
  zero!(f)
  d = f
  b = basis(parent(f))
  for i=1:n
    f += b[i]*L[1, i+n]
    d += b[i]*L[1, i]
  end
#  @show f, d
  return f//d
end

function induce_reco!(last::Array{Nemo.Generic.MPoly{nf_elem}, 1}, Res::Array{Nemo.Generic.MPoly{nf_elem}, 1}, K::AnticNumberField, p::fmpz, f::fmpz_poly, rec = reco_den_alg)
  data = reco_init(K, p, f)
  Kx = parent(Res[1])
  fl = true
  for i=1:length(Res)
    r = deepcopy(Res[i])
    for j=1:Res[i].length
      r.coeffs[j] = rec(data, Res[i].coeffs[j])
    end
    if i > length(last) || r != last[i]
      fl = false
    end
    if i > length(last)
      push!(last, r)
    else
      last[i] = r
    end
  end
  return fl
end

function modstd(I::Array{Nemo.Generic.MPoly{nf_elem}, 1}, rec = reco)
  ZX, X = FlintZZ["X"]
  p = 2^30
  Res = []
  pp = fmpz(1)

  Kx = parent(I[1])
  K = base_ring(Kx)
  last = elem_type(Kx)[]

  nb = 100
  while true
    p = next_prime(p)
    R = Nemo.ResidueRing(FlintZZ, p)
    Rt, t = R["t"]
    lp = [ x for x = keys(Nemo.factor(Rt(K.pol)).fac) if degree(x) == 1]
    if length(lp) < 1
      continue
    end
    Ip = to_singular(I, lp[1])
    Gp = Singular.std(Ip, complete_reduction = true)
    if isone(pp)
      Res = from_singular(Gp, parent(I[1]))
      pp = fmpz(p)
      f = lift(ZX, lp[1])
    else
      Res = from_singular_crt(Gp, Res, pp)
      f = induce_crt(lift(ZX, lp[1]), fmpz(p), f, pp)[1]
      pp *= p
    end
    if nbits(pp) > nb
      if induce_reco!(last, Res, K, pp, f, rec)
        return last
      end
      nb *= 2
    end
    if nbits(pp) > 1000
      return Res, pp, f
    end  
  end
end  

