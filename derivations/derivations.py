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
from sympy.functions.elementary.exponential import exp, log
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

    cpfunc = (R * (a[i, 0] + T * (a[i, 1] + T * (a[i, 2] + T * (a[i, 3] + a[i, 4] * T))))) / Wi[i]
    cp = IndexedFunc('{c_p}', T)
    cp_tot_sym = ImplicitSymbol(r'\bar{c_p}', T)
    cp_tot = Sum(Yi_sym[i] * cp[i], (i, 1, Ns))
    write_eq(cp_tot_sym, cp_tot)

    write_eq(Eq(cp[i], cpfunc))
    write_eq(Eq(diff(cp[i], T), simplify(diff(cpfunc, T))))

    h = (R * T * (a[i, 0] + T * (a[i, 1] * Rational(1, 2) + T * (a[i, 2] * Rational(1, 3) + T * (a[i, 3] * Rational(1, 4) + a[i, 4] * T * Rational(1, 5)))))) / Wi[i]
    hi = IndexedFunc('h', T)
    write_eq(Eq(hi[i], h))
    write_eq(Eq(diff(hi[i], T), simplify(diff(h, T))))

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


    dTdt_sym = diff(T, t)
    dTdt = -1 / (density_sym * cp_tot_sym) * Sum(hi[i] * Wi[i] * omega_sym[i], (i, 1, Ns))
    write_eq(diff(T, t), dTdt)

    dTdt = dTdt.subs(density_sym, W_sym * Ctot_sym)
    write_eq(diff(T, t), dTdt)

    cp_tot = cp_tot.subs(Sum(cp[i] * Yi_sym[i], (i, 1, Ns)), Sum(cp[i] * Yi, (i, 1, Ns)))
    write_eq(cp_tot_sym, cp_tot)
    cp_tot = simplify(cp_tot).subs(density_sym, W_sym * Ctot_sym)
    write_eq(cp_tot_sym, cp_tot)

    dTdt = dTdt.subs(W_sym * Ctot_sym * cp_tot_sym, W_sym * Ctot_sym * cp_tot)

    write_eq(diff(T, t), dTdt)

    dTdt = dTdt.subs(Sum(Wi[i] * Ci[i] * cp[i], (i, 1, Ns)),
        Sum(Wi[i] * Ci[i] * cp[i], (i, 1, Ns - 1)) + Wi[Ns] * Cns * cp[Ns])

    write_eq(diff(T, t), dTdt)

    num, den = fraction(dTdt)
    new_den = Sum(Ci[i] * (Wi[i] * cp[i] - Wi[Ns] * cp[Ns]), (i, 1, Ns - 1)) + Wi[Ns] * cp[Ns] * Ctot

    assert(simplify(den - new_den) == 0)

    dTdt = num / new_den.subs(Ctot, Ctot_sym)
    write_eq(diff(T, t), dTdt)

    #Temperature jacobian entries

    #first we do the concentration derivative
    dTdC_sym = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    #need to do some trickery here to get the right derivative
    #due to weirdness with differentiation of indxedfunc's
    num, den = fraction(dTdt)

    omega_i = Function(r'\dot{\omega}_i')(Ci, T, i)

    num = Sum(Wi[i] * omega_i * hi[i], (i, 1, Ns))
    dTdt_new = num / den
    write_eq(diff(T, t), dTdt_new)

    dTdC = diff(dTdt_new, Ci[j])
    write_eq(dTdC_sym, dTdC)
    dTdC = simplify(dTdC)
    write_eq(dTdC_sym, dTdC)

    #make it more compact for sanity
    num, den = fraction(dTdC)
    subs_expr_den, power = den.args[:]
    subs_expr_num = Add.make_args(subs_expr_den)
    sum_term = next(term for term in subs_expr_num if term.has(Sum))
    subs_expr_num = Add(*[x for x in subs_expr_num if x != sum_term]) + simplify(sum_term)
    
    dTdC = num.subs(subs_expr_num, Sum(Wi[i] * Ci[i] * cp[i], (i, 1, Ns))) / den.subs(
        subs_expr_den, Sum(Wi[i] * Ci[i] * cp[i], (i, 1, Ns)))

    write_eq(dTdC_sym, dTdC)

    #one more level of compactness, replaces the kronecker delta sum
    num, den = fraction(dTdC)
    num_terms = Add.make_args(num)
    kd_term = next(x for x in num_terms if x.has(KroneckerDelta))
    num_terms = Add(*[x for x in num_terms if x != kd_term])
    kd_term = kd_term.subs(Sum((Wi[Ns] * cp[Ns] - Wi[i] * cp[i]) * KroneckerDelta(i, j), (i, 1, Ns - 1)),
        (Wi[Ns] * cp[Ns] - Wi[j] * cp[j]))
    dTdC = (num_terms + kd_term) / den
    write_eq(dTdC_sym, dTdC)

    dTdtdT = symbols(r'\frac{\partial\dot{T}}{\partial{T}}')
    write_eq(Eq(dTdtdT, simplify(diff(dTdt_new, T))))

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
    