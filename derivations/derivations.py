from sympy.interactive import init_printing
from sympy.simplify.radsimp import collect, fraction
from sympy.simplify.simplify import simplify, cancel, separatevars, sum_simplify, signsimp
from sympy.solvers.solvers import solve
from sympy.core.symbol import symbols, Symbol
from sympy.core.relational import Eq
from sympy.core.sympify import sympify
from sympy.core.mul import Mul
from sympy.core.add import Add
from sympy.core.power import Pow
from sympy.tensor.indexed import Idx, IndexedBase
from sympy.concrete import Sum, Product
from sympy.printing.latex import LatexPrinter
from sympy.core.function import UndefinedFunction, Function, diff, Derivative, expand, expand_mul
from sympy.functions.elementary.exponential import exp, log, sqrt
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.numbers import Rational
from sympy.core.exprtools import factor_terms
from sympy.core.relational import Equality
from sympy.core.singleton import S


from constants import *
from sympy_addons import *

init_printing()

class CustomLatexPrinter(LatexPrinter):
    pass

#override default latex print method
def latex(expr, **settings):
    return CustomLatexPrinter(settings).doprint(expr)

#some custom behaviour for concentrations
class IndexedConc(IndexedFunc):
    is_Real = True
    is_Positive = True
    is_Negative = False
    is_Number = True
    _diff_wrt = True
    def _eval_derivative(self, wrt):
        if isinstance(wrt, IndexedFunc.IndexedFuncValue) and \
            isinstance(wrt.base, IndexedConc):
            return Symbol(r'\frac{{\partial[C]}}{{\partial{}}}'.format(
                wrt))
        return S.Zero
"""
Actual derivation
"""

def write_eq(*args):
    if len(args) == 2:
        file.write(latex(Eq(args[0], args[1]), mode='equation') + '\n')
    else:
        file.write(latex(*args, mode='equation') + '\n')

def write_dummy_eq(text):
    file.write(r'\begin{equation}' + text + r'\end{equation}' + '\n')


def factor_and_solve(expr, factor, sum_simplify=True):
    if isinstance(expr, Equality):
        expr = expr.lhs - expr.rhs
    expr = collect(expand(expr), factor)
    args = Add.make_args(expr)
    fac_args = [i for i, arg in enumerate(args) if arg.has(factor)]
    noFac_args = [i for i in range(len(args)) if i not in fac_args]
    if len(fac_args) == 1:
        fac_args = args[fac_args[0]]
    else:
        fac_args = Add(*[args[i] for i in fac_args])
    if len(noFac_args) == 1:
        noFac_args = args[noFac_args[0]]
    else:
        noFac_args = Add(*[args[i] for i in noFac_args])
    if sum_simplify:
        return -sum_simplifier(noFac_args) / sum_simplifier(fac_args / factor)
    else:
        return -(noFac_args) / (fac_args / factor)

def sum_simplifier(expr):
    args = Mul.make_args(expr)
    out_args = []
    for arg in args:
        if isinstance(arg, Sum):
            out_args.append(simplify(arg))
        elif isinstance(arg, Mul):
            out_args.append(sum_simplifier(arg))
        elif isinstance(arg, Add):
            out_args.append(
                simplify(Add(*[sum_simplifier(x) for x in arg.args])))
        else:
            out_args.append(simplify(arg))
    return Mul(*out_args)

def conp_derivation(file):
    #mechanism size
    Ns = S.Ns
    Nr = S.Nr

    #index variables
    i = Idx('i', (1, Ns + 1))
    j = Idx('j', (1, Nr + 1))
    k = Idx('k')

    #time
    t = symbols('t', float=True, finite=True, negative=False, real=True)


    #thermo vars
    T = ImplicitSymbol('T', t)
    Ci = IndexedConc('[C]', t)
    Wi = IndexedBase('W')

    #some constants, and state variables
    Patm = S.atm_pressure
    R = S.gas_constant
    m_sym = S.mass

    #define concentration
    P = S.pressure
    V_sym = ImplicitSymbol('V', t)
    V = V_sym
    state_vec = [T, Ci[1], Ci[2], Ci[Ns]]

    #define state vector
    state_vec_str = ' = ' + r'\left\{{{}\ldots {}\right\}}'
    state = ImplicitSymbol(r'\Phi', t)
    write_dummy_eq(str(state) + state_vec_str.format(
        ','.join([str(x) for x in state_vec[:-1]]),
        str(state_vec[-1])))

    write_dummy_eq(str(diff(state, t)) + state_vec_str.format(
        ','.join([str(diff(x, t)) for x in state_vec[:-1]]),
        str(diff(state_vec[-1], t))))

    n_sym = ImplicitSymbol('n', t)
    n = P * V / (R * T)
    write_eq(n_sym, n)

    Ctot_sym = ImplicitSymbol('[C]', t)
    Ctot = P / (R * T)
    write_eq(Ctot_sym, Ctot)
    Cns_sym = ImplicitSymbol('[C]_{N_s}', args=(P, T))
    Cns = Ctot - Sum(Ci[i], (i, 1 , Ns - 1))
    write_eq(Cns_sym, Cns)

    #molecular weight
    Cns_simp = 1 - Sum(Ci[i], (i, 1 , Ns - 1)) / Ctot
    assert expand(Cns / Ctot) - expand(Cns_simp) == 0
    W = Sum(Wi[i] * Ci[i], (i, 1, Ns - 1)) / Ctot_sym + Wi[Ns] * Cns_simp.subs(1 / Ctot, 1 / Ctot_sym)
    W_new = Wi[Ns] + Sum(Ci[i] * (Wi[i] - Wi[Ns]), (i, 1, Ns - 1)) / Ctot_sym
    assert simplify(W - W_new) == 0
    W = W_new
    
    W_sym = ImplicitSymbol('W', t)
    write_eq(W_sym, W)

    m = n * W
    density = m / V
    density_sym = ImplicitSymbol(r'\rho', t)
    write_eq(density_sym, n_sym * W_sym / V_sym)

    #mass fractions
    Yi_sym = IndexedFunc('Y', args=(density, Ci[i], Wi[i]))
    Yi = Ci[i] * Wi[i]/ density_sym

    write_eq(Yi_sym[i], Yi)

    #polyfits
    a = IndexedBase('a')

    cpfunc = (R * (a[i, 0] + T * (a[i, 1] + T * (a[i, 2] + T * (a[i, 3] + a[i, 4] * T)))))
    cp = IndexedFunc(r'{c_p}^{\circ}', T)
    cp_mass = IndexedFunc(r'{c_p}', T)

    cp_tot_sym = ImplicitSymbol(r'\bar{c_p}', T,)
    cp_tot = Sum(Yi_sym[i] * cp_mass[i], (i, 1, Ns))
    write_eq(cp_tot_sym, cp_tot)

    write_eq(Eq(cp[i], cpfunc))
    write_eq(Eq(diff(cp[i], T), simplify(diff(cpfunc, T))))
    write_eq(cp_mass[i], cp[i] / Wi[i])

    h = (R * T * (a[i, 0] + T * (a[i, 1] * Rational(1, 2) + T * (a[i, 2] * Rational(1, 3) + T * (a[i, 3] * Rational(1, 4) + a[i, 4] * T * Rational(1, 5))))))
    hi = IndexedFunc(r'h^{\circ}', T)
    hi_mass = IndexedFunc(r'h', T)
    write_eq(hi[i], h)
    write_eq(diff(hi[i], T), simplify(diff(h, T)))
    write_eq(hi_mass[i], hi[i] / Wi[i])

    B = a[i, 6] - a[i, 0] + (a[i, 0] - 1) * log(T) + T * (a[i, 1] * Rational(1, 2) + T * (a[i, 2] * Rational(1, 6)  + T * (a[i, 3] * Rational(1, 12)  + a[i, 4] * T * Rational(1, 20)))) - a[i, 5] / T 
    B_sym = IndexedFunc(r'B', T)

    write_eq(Eq(B_sym[i], B))
    write_eq(Eq(diff(B_sym[i], T), simplify(diff(B, T))))

    #reaction rates

    #arrhenius
    A = IndexedBase(r'A')
    b = IndexedBase(r'b')
    Ea = IndexedBase(r'{E_{a}}')
    kf_sym = IndexedFunc(r'{k_f}', T)

    #forward reaction rates
    kf = A[j] * (T**b[j]) * exp(-Ea[j] / (R * T))
    write_eq(Eq(kf_sym[j], kf))

    #derivs
    dkf_dt = diff(kf, T)
    write_eq(Eq(diff(kf_sym[j], T), dkf_dt))

    #stoiciometric coefficients
    nu_f = IndexedBase(r'\nu^{\prime}')
    nu_r = IndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[i, j] - nu_r[i, j]
    nu_sym = IndexedBase(r'\nu')
    write_eq(Eq(nu_sym[i, j], nu))

    #equilibrium
    Kc = ((Patm / T)**Sum(nu_sym[i, j], (i, 1, Ns))) * exp(Sum(nu_sym[i, j] * B_sym[i], (i, 1, Ns)))
    Kc_sym = IndexedFunc(r'{K_c}', T)
    write_eq(Eq(Kc_sym[j], Kc))

    #temperature deriv
    dkc_dt = simplify(diff(Kc, T))
    write_eq(Eq(diff(Kc_sym[j], T), dkc_dt))

    #reverse reaction rate
    kr = kf / Kc
    kr_sym = kf_sym[j] / Kc_sym[j]

    #rate of progress
    rop = kf_sym[j] * SmartProduct(Ci[i]**nu_f[i, j], (i, 1, Ns)) - kr_sym * SmartProduct(Ci[i]**nu_r[i, j], (i, 1, Ns))
    rop_sym = IndexedFunc(r'{R_{net}}', args=(Ci, T, nu))

    write_eq(Eq(rop_sym[j], rop))
    
    #net reaction rate
    omega = Sum(rop, (j, 1, Nr))
    omega_sym = IndexedFunc(Symbol(r'\dot{\omega}'), args=(Ci[i], T, nu))

    write_eq(Eq(diff(Ci[i], t), Eq(omega_sym[i], omega)))

    #temperature derivative

    #in terms of mass fraction

    dTdt_sym = diff(T, t)
    dTdt = -1 / (density_sym * cp_tot_sym) * Sum(hi_mass[i] * Wi[i] * omega_sym[i], (i, 1, Ns))
    write_eq(diff(T, t), dTdt)

    #next we turn into concentrations
    dTdt = dTdt.subs(density_sym, W_sym * Ctot_sym)
    write_eq(diff(T, t), dTdt)

    #do some simplifcation of the cp term
    cp_tot = cp_tot.subs(Sum(cp_mass[i] * Yi_sym[i], (i, 1, Ns)), Sum(cp_mass[i] * Yi, (i, 1, Ns)))
    write_eq(cp_tot_sym, cp_tot)
    cp_tot = simplify(cp_tot).subs(density_sym, W_sym * Ctot_sym)
    write_eq(cp_tot_sym, cp_tot)

    dTdt = dTdt.subs(W_sym * Ctot_sym * cp_tot_sym, W_sym * Ctot_sym * cp_tot)
    write_eq(dTdt_sym, dTdt)

    #this will be used many times
    CiCpSum = Sum(Ci[i] * cp[i], (i, 1, Ns))

    #next we swap out the mass cp's
    dTdt = dTdt.subs(Sum(Wi[i] * Ci[i] * cp_mass[i], (i, 1, Ns)), CiCpSum).subs(
        Sum(hi_mass[i] * Wi[i] * omega_sym[i], (i, 1, Ns)),
        Sum(hi[i] * omega_sym[i], (i, 1, Ns)))

    #save a copy of this form as it's very compact
    dTdt_simple = dTdt

    write_eq(diff(T, t), dTdt)

    #next expand the summation for derivative taking
    dTdt = dTdt.subs(CiCpSum,
        Sum(Ci[i] * cp[i], (i, 1, Ns - 1)) + Cns * cp[Ns])

    write_eq(diff(T, t), dTdt)

    num, den = fraction(dTdt)
    new_den = Sum(Ci[i] * (cp[i] - cp[Ns]), (i, 1, Ns - 1)) + cp[Ns] * Ctot

    assert(simplify(den - new_den) == 0)

    dTdt = num / new_den.subs(Ctot, Ctot_sym)
    write_eq(diff(T, t), dTdt)

    #Temperature jacobian entries

    #first we do the concentration derivative
    dTdotdC_sym = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    #need to do some trickery here to get the right derivative
    #due to weirdness with differentiation of indxedfunc's
    num, den = fraction(dTdt)

    omega_i = Function(r'\dot{\omega}_i')(Ci, T, i)

    num = Sum(omega_i * hi[i], (i, 1, Ns))
    dTdt_new = num / den
    write_eq(diff(T, t), dTdt_new)

    dTdotdC = diff(dTdt_new, Ci[j])
    write_eq(dTdotdC_sym, dTdotdC)
    dTdotdC = simplify(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)

    #make it more compact for sanity
    def __collapse_cp_conc_sum(expr):
        terms = Add.make_args(expr)
        subs_terms = []
        for term in terms:
            num, den = fraction(term)
            #denominator is a power of the sum
            if isinstance(den, Pow):
                subs_term_den, power = den.args[:]
            else:
                subs_term_den = den
            subs_term_num = simplify(subs_term_den)
            num = num.subs(subs_term_num, CiCpSum).subs(
                subs_term_den, CiCpSum)
            den = den.subs(subs_term_num, CiCpSum).subs(
                subs_term_den, CiCpSum)
            subs_terms.append(num / den)

        return Add(*subs_terms)

    dTdotdC = __collapse_cp_conc_sum(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)

    #another level of compactness, replaces the kronecker delta sum
    num, den = fraction(dTdotdC)
    num_terms = Add.make_args(num)
    kd_term = next(x for x in num_terms if x.has(KroneckerDelta))
    num_terms = Add(*[x for x in num_terms if x != kd_term])
    kd_term = kd_term.subs(Sum((cp[Ns] - cp[i]) * KroneckerDelta(i, j), (i, 1, Ns - 1)),
        (cp[Ns] - cp[j]))
    dTdotdC = (num_terms + kd_term) / den
    write_eq(dTdotdC_sym, dTdotdC)

    #now expand to replace with the dT/dt term
    def __factor_denom(expr):
        num, den = fraction(expr)
        arg, power = den.args
        assert power == 2
        return Add(*[x / arg for x in Add.make_args(num)]) / arg

    dTdotdC = __factor_denom(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)

    def __rep_dT_dt(expr):
        #the terms here should be some denominator
        #which we do not consider
        #multiplied by some add's
        #one of which contains the dTdt term
        expr = expr.subs(omega_i, omega_sym[i])

        num, den = fraction(expr)
        out_terms = []
        add_terms = Add.make_args(num)
        for term in add_terms:
            if term.has(Ci[i]) and term.has(cp[i]) and term.has(omega_sym[i])\
                and term.has(hi[i]) and term.has(Sum):
                #this is the one
                assert isinstance(term, Mul)
                subterms = Mul.make_args(term)
                out_sub_terms = []
                for sterm in subterms:
                    n, d = fraction(sterm)
                    if d == CiCpSum:
                        continue
                    elif n == Sum(omega_sym[i] * hi[i], (i, 1, Ns)):
                        continue
                    out_sub_terms.append(sterm)
                out_terms.append(Mul(*out_sub_terms) * dTdt_sym)
            else:
                out_terms.append(term)

        return Add(*out_terms) / den 


    dTdotdC = __rep_dT_dt(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)


    #up next the temperature derivative
    dTdotdT_sym = symbols(r'\frac{\partial\dot{T}}{\partial{T}}')
    #first we must sub in the actual form of C, as the temperature derivative is non-zero
    starting = dTdt_new.subs(Ctot_sym, Ctot)
    write_eq(dTdt_sym, starting)
    dTdotdT = diff(starting, T)

    write_eq(dTdotdT_sym, dTdotdT)

    #first up, go back to Ctot_sym
    dTdotdT = dTdotdT.subs(Ctot, Ctot_sym)
    write_eq(dTdotdT_sym, dTdotdT)

    #and collapse the cp sum
    dTdotdT = __collapse_cp_conc_sum(dTdotdT)
    write_eq(dTdotdT_sym, dTdotdT)

    #now we factor out the ci cp sum
    dTdotdT = factor_terms(dTdotdT, CiCpSum)
    write_eq(dTdotdT_sym, dTdotdT)

    #and replace the dTdt term
    dTdotdT = __rep_dT_dt(dTdotdT)
    write_eq(dTdotdT_sym, dTdotdT)

    #the final simplification is of the [C]cp[ns] term
    dTdotdT = dTdotdT.subs(Ctot_sym * diff(cp[Ns], T), diff(cp[Ns], T) * Sum(Ci[i], (i, 1, Ns)))
    write_eq(dTdotdT_sym, dTdotdT)

    num, den = fraction(dTdotdT)
    #seach for the Ci sums
    add_terms = Add.make_args(num)
    simp_term = next(x for x in add_terms if x.has(Sum) and x.has(Ci[i]))
    add_terms = [x for x in add_terms if x != simp_term]
    to_simp = Mul.make_args(simp_term)
    constant = Mul(*[x for x in to_simp if not (x.has(Ci[i]) and x.has(Sum))])
    to_simp = next(x for x in to_simp if not constant.has(x))
    #we now have the Ci sum

    #make sure it's the right thing
    check_term = -diff(cp[Ns], T) * Sum(Ci[i], (i, 1, Ns))\
        + Sum((diff(cp[Ns], T) - diff(cp[i], T)) * Ci[i], (i, 1, Ns - 1))
    other_add = Ctot_sym * cp[Ns] / T
    assert simplify(to_simp - (check_term + other_add)) == 0

    #make the replacement term
    rep_term = -diff(cp[Ns], T) * Sum(Ci[i], (i, 1, Ns - 1)) + -diff(cp[Ns], T) * Ci[Ns] +\
                    Sum((diff(cp[Ns], T) - diff(cp[i], T)) * Ci[i], (i, 1, Ns - 1))
    assert simplify(rep_term - (-Sum(diff(cp[i], T) * Ci[i], (i, 1, Ns - 1)) 
                - diff(cp[Ns], T) * Ci[Ns])) == 0

    #and reconstruct
    add_terms.append(constant * (-Sum(Ci[i] * diff(cp[i], T), (i, 1, Ns)) + 
        other_add))
    dTdotdT = Add(*add_terms) / den
    write_eq(dTdotdT_sym, dTdotdT)

    return

    #concentration Jacobian equations
    dCdot = IndexedFunc(r'\dot{C}', (Ci[k], T))
    write_eq(Eq(diff(dCdot[i], Ci[j]), simplify(diff(omega, Ci[k]))))
    write_eq(Eq(diff(dCdot[i], T), simplify(diff(omega, T))))


if __name__ == '__main__':
    class filer(object):
        def __init__(self, name, mode):
            self.name = name
            self.mode = mode
            self.lines = []
        def write(self, thestr):
            self.lines.append(thestr)
        def close(self):
            with open(self.name, self.mode) as file:
                file.writelines(self.lines)

    file = filer('derivations/derivs.tex', 'w')
    file.write(r'\documentclass[a4paper,10pt]{article}' + '\n' +
               r'\usepackage[utf8]{inputenc}' + '\n'
               r'\usepackage{amsmath}' + '\n' +
               r'\usepackage{breqn}' + '\n')
    file.write(r'\begin{document}' + '\n')
    def finalize():
        file.write(r'\end{document}' + '\n')
        file.lines = [line.replace(r'\begin{equation}', r'\begin{dmath} ').replace(
            r'\end{equation}', r'\end{dmath}') for line in file.lines]
        file.close()
    conp_derivation(file)
    finalize()
    