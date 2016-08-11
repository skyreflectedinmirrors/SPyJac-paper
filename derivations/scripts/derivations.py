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
import os

home_dir = os.path.dirname(os.path.realpath(__file__))
out_dir = os.path.realpath(os.path.join(
    home_dir, '..', 'tex'))

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

def write_eq(*args, **kw_args):
    writer = file if not 'myfile' in kw_args else kw_args['myfile']
    if len(args) == 2:
        writer.write(latex(Eq(args[0], args[1]), mode='equation') + '\n')
    else:
        file.write(latex(*args, mode='equation') + '\n')

def write_dummy_eq(text, **kw_args):
    writer = file if not 'myfile' in kw_args else kw_args['myfile']
    writer.write(r'\begin{equation}' + text + r'\end{equation}' + '\n')

"""
ConP / ConV independent symbols
"""

#time
t = symbols('t', float=True, finite=True, negative=False, real=True)


#thermo vars
T = ImplicitSymbol('T', t)  

#mechanism size
Ns = S.Ns
Nr = S.Nr

#index variables
k = Idx('k', (1, Ns + 1))
i = Idx('i', (1, Nr + 1))
j = Idx('j')

Wi = IndexedBase('W')

#some constants, and state variables
Patm = S.atm_pressure
R = S.gas_constant
m_sym = S.mass

#polyfits
a = IndexedBase('a')


def thermo_derivation(Yi_sym, subfile=None):
    def write(*args):
        write_eq(*args, myfile=subfile)
    #derivation of thermo constants, e.g. enthalpy, cp, etc.

    cpfunc = R * (a[k, 0] + T * (a[k, 1] + T * (a[k, 2] + T * (a[k, 3] + a[k, 4] * T))))
    cp = IndexedFunc(r'{C_p}', T)
    cp_mass = IndexedFunc(r'{c_p}', T)

    cp_tot_sym = ImplicitSymbol(r'\bar{c_p}', T,)
    if hasattr(Yi_sym, '__getitem__'):
        Yi_sym = Yi_sym[k]

    cp_tot = Sum(Yi_sym * cp_mass[k], (k, 1, Ns))
    if subfile:
        write(Eq(Eq(Symbol(r'{C_{p,k}}^{\circ}'), cp[k]), cpfunc),
            expand(cpfunc))
        write(diff(cp[k], T), simplify(diff(cpfunc, T)))
        write(cp_mass[k], cp[k] / Wi[k])
        write(cp_tot_sym, cp_tot)

    hfunc = R * (T * (a[k, 0] + T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 3) + T * (a[k, 3] * Rational(1, 4) + a[k, 4] * T * Rational(1, 5))))) + a[k, 5])
    h = IndexedFunc(r'H', T)
    h_mass = IndexedFunc(r'h', T)

    #check that the dH/dT = cp identity holds
    if subfile: #only check once
        assert simplify(diff(hfunc, T) - cpfunc) == 0

    if subfile:
        write(Eq(Eq(Symbol(r'H_k^{\circ}'), h[k]), hfunc),
            expand(hfunc))
        write(diff(h[k], T), simplify(diff(hfunc, T)))
        write(h_mass[k], h[k] / Wi[k])

    #finally do the entropy and B terms
    Sfunc = R * (a[k, 0] * log(T) + T * (a[k, 1] + T * (a[k, 2] * Rational(1, 2) + T * (a[k, 3] * Rational(1, 3) + a[k, 4] * T * Rational(1, 4)))) + a[k, 6])
    s = IndexedFunc(r'S', T)
    if subfile:
        write(Eq(Eq(Symbol(r'S_k^{\circ}'), s[k]), Sfunc), 
            expand(Sfunc))

    Bk = Sfunc / R - hfunc / (R * T)

    Bk_rep = a[k, 6] + a[k, 0] * (log(T) - 1) + T *\
                (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 6) +\
                    T * (a[k, 3] * Rational(1, 12) + a[k, 4] * Rational(1, 20) * T))) -\
                a[k, 5] / T

    if subfile:
        write(Symbol('B_k'), Bk_rep)
        #only check once
        assert simplify(Bk - Bk_rep) == 0

        diff_bk_rep = ((a[k, 5] / T) + a[k, 0]) / T + \
            a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 3) + T *(a[k, 3] *\
                Rational(1, 4) + T * a[k, 4] * Rational(1, 5)))

        #only check once
        assert simplify(diff(Bk, T) - diff_bk_rep) == 0
        write(diff(ImplicitSymbol('B_k', T), T), diff_bk_rep)

    return cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass, Bk_rep

def reaction_derivation(P, Ck, Bk, subfile):
    def write(*args):
        write_eq(*args, myfile=subfile)
    def write_dummy(*args):
        write_dummy_eq(*args, myfile=subfile)
    nu_f = IndexedBase(r'\nu^{\prime}')
    nu_r = IndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[k, i] - nu_r[k, i]
    nu_sym = IndexedBase(r'\nu')
    write(nu_sym[k, i], nu)

    #define for later use
    Ctot = P / (R * T)

    omega_sym = IndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck, T, nu, P))
    write(diff(Ck[k], t), omega_sym[k])

    q = IndexedFunc('q', args=(Ck, T, P))
    omega_k = Sum(nu_sym[k, i] * q[i], (i, 1, Nr))
    write(omega_sym[k], omega_k)

    Rop = IndexedFunc('R', args=(Ck, T))
    ci = IndexedFunc('c', args=(Ck, P))

    write(q[i], Rop[i] * ci[i])

    #arrhenius coeffs
    A = IndexedBase(r'A')
    b = IndexedBase(r'b')
    Ea = IndexedBase(r'{E_{a}}')

    #rate of progress
    Ropf_sym = IndexedFunc(r'{R_f}', args=(Ck, T))
    Ropr_sym = IndexedFunc(r'{R_r}', args=(Ck, T))

    write(Rop[i], Ropf_sym[i] - Ropr_sym[i])

    kf_sym = IndexedFunc(r'{k_f}', T)
    Ropf = kf_sym * SmartProduct(Ck[k]**nu_f[k, i], (k, 1, Ns))
    write(Ropf_sym, Ropf)

    kr_sym = IndexedFunc(r'{k_r}', T)
    Ropr = kr_sym * SmartProduct(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write(Ropr_sym, Ropr)

    #write the various ci forms
    ci_elem = 1
    write_dummy('c_{{i}} = {}'.format(ci_elem) + r'\text{\quad for elementary reactions}')

    ci_thd = ImplicitSymbol('[X]', args=(Ck, Ctot))
    write_dummy('c_{{i}} = {}'.format(latex(ci_thd)) + r'\text{\quad for third-body enhanced reactions}')

    Pri = ImplicitSymbol('P_{r, i}', args=(T, Ck, Ctot))
    Fi = ImplicitSymbol('F_{i}', args=(T, Pri))
    ci_fall = (Pri / (1 + Pri)) * Fi 
    write_dummy('c_{{i}} = {}'.format(latex(ci_fall)) + r'\text{\quad for unimolecular/recombination falloff reactions}')

    ci_chem = (1 / (1 + Pri)) * Fi  
    write_dummy('c_{{i}} = {}'.format(latex(ci_fall)) + r'\text{\quad for chemically-activated bimolecular reactions}')

    #forward reaction rate
    kf = A[i] * (T**b[i]) * exp(-Ea[i] / (R * T))
    write(kf_sym[i], kf)

    
    #equilibrium
    Kp_sym = IndexedFunc(r'{K_p}', args=(T, a))
    Kc_sym = IndexedFunc(r'{K_c}', args=(T))
    write(Kc_sym[i], Kp_sym[i] * ((Patm / T)**Sum(nu_sym[k, i], (k, 1, Ns))))

    write_dummy(latex(Kp_sym[i]) + ' = ' + 
        r'\text{exp}(\frac{\Delta S^{\circ}_k}{R_u} - \frac{\Delta H^{\circ}_k}{R_u T})')
    write_dummy(latex(Kp_sym[i]) + ' = ' + 
        r'\text{exp}(\sum_{k=1}^{N_s}\frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T})')

    B_sym = IndexedFunc('B', T)
    Kc = ((Patm / T)**Sum(nu_sym[k, i], (k, 1, Ns))) * exp(Sum(nu_sym[k, i] * B_sym[k], (k, 1, Ns)))
    write(Kc_sym[i], Kc)

    write_dummy(latex(B_sym[k]) + r'= \frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T}')

    write(B_sym[k], simplify(factor_terms(Bk, T)))

    #reverse reaction rate
    kr = kf / Kc
    kr_sym = IndexedFunc(r'{k_r}', kf_sym[i] / Kc_sym[i])
    write(kr_sym[i], kf_sym[i] / Kc_sym[i])
    

    return nu_sym, nu, omega_sym, omega_k, q, Rop, ci



def conp_derivation(file):
    #thermo vars
    Ck = IndexedConc('[C]', t)

    #define concentration
    P = S.pressure
    V_sym = ImplicitSymbol('V', t)
    V = V_sym
    state_vec = [T, Ck[1], Ck[2], Ck[Ns]]

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
    Cns = Ctot - Sum(Ck[k], (k, 1 , Ns - 1))
    write_eq(Cns_sym, Cns)

    #molecular weight
    Cns_simp = 1 - Sum(Ck[k], (k, 1 , Ns - 1)) / Ctot
    assert expand(Cns / Ctot) - expand(Cns_simp) == 0
    W = Sum(Wi[k] * Ck[k], (k, 1, Ns - 1)) / Ctot_sym + Wi[Ns] * Cns_simp.subs(1 / Ctot, 1 / Ctot_sym)
    W_new = Wi[Ns] + Sum(Ck[k] * (Wi[k] - Wi[Ns]), (k, 1, Ns - 1)) / Ctot_sym
    assert simplify(W - W_new) == 0
    W = W_new
    
    W_sym = ImplicitSymbol('W', t)
    write_eq(W_sym, W)

    m = n * W
    density = m / V
    density_sym = ImplicitSymbol(r'\rho', t)
    write_eq(density_sym, n_sym * W_sym / V_sym)

    #mass fractions
    Yi_sym = IndexedFunc('Y', args=(density, Ck[k], Wi[k]))
    Yi = Ck[k] * Wi[k]/ density_sym

    write_eq(Yi_sym[k], Yi)

    #get all our thermo symbols
    cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass, Bk = thermo_derivation(Yi)

    #reaction rates

    with filer('conp_reaction_derivation.tex', 'w') as subfile:
        reaction_derivation(P, Ck, Bk, subfile)

    return

    #rate of progress
    rop = kf_sym[i] * SmartProduct(Ck[k]**nu_f[k, i], (k, 1, Ns)) - kr_sym * SmartProduct(Ck[k]**nu_r[k, i], (k, 1, Ns))
    rop_sym = IndexedFunc(r'{R_{net}}', args=(Ck, T, nu))

    write_eq(Eq(rop_sym[i], rop))
    
    #net reaction rate
    omega = Sum(rop, (i, 1, Nr))
    omega_sym = IndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck[k], T, nu))

    write_eq(Eq(diff(Ck[k], t), Eq(omega_sym[k], omega)))

    #temperature derivative

    #in terms of mass fraction

    dTdt_sym = diff(T, t)
    dTdt = -1 / (density_sym * cp_tot_sym) * Sum(h_mass[k] * Wi[k] * omega_sym[k], (k, 1, Ns))
    write_eq(diff(T, t), dTdt)

    #next we turn into concentrations
    dTdt = dTdt.subs(density_sym, W_sym * Ctot_sym)
    write_eq(diff(T, t), dTdt)

    #do some simplifcation of the cp term
    cp_tot = cp_tot.subs(Sum(cp_mass[k] * Yi_sym[k], (k, 1, Ns)), Sum(cp_mass[k] * Yi, (k, 1, Ns)))
    write_eq(cp_tot_sym, cp_tot)
    cp_tot = simplify(cp_tot).subs(density_sym, W_sym * Ctot_sym)
    write_eq(cp_tot_sym, cp_tot)

    dTdt = dTdt.subs(W_sym * Ctot_sym * cp_tot_sym, W_sym * Ctot_sym * cp_tot)
    write_eq(dTdt_sym, dTdt)

    #this will be used many times
    CkCpSum = Sum(Ck[k] * cp[k], (k, 1, Ns))

    #next we swap out the mass cp's
    dTdt = dTdt.subs(Sum(Wi[k] * Ck[k] * cp_mass[k], (k, 1, Ns)), CkCpSum).subs(
        Sum(h_mass[k] * Wi[k] * omega_sym[k], (k, 1, Ns)),
        Sum(h[k] * omega_sym[k], (k, 1, Ns)))

    #save a copy of this form as it's very compact
    dTdt_simple = dTdt

    write_eq(diff(T, t), dTdt)

    #next expand the summation for derivative taking
    dTdt = dTdt.subs(CkCpSum,
        Sum(Ck[k] * cp[k], (k, 1, Ns - 1)) + Cns * cp[Ns])

    write_eq(diff(T, t), dTdt)

    num, den = fraction(dTdt)
    new_den = Sum(Ck[k] * (cp[k] - cp[Ns]), (k, 1, Ns - 1)) + cp[Ns] * Ctot

    assert(simplify(den - new_den) == 0)

    dTdt = num / new_den.subs(Ctot, Ctot_sym)
    write_eq(diff(T, t), dTdt)

    #Temperature jacobian entries

    #first we do the concentration derivative
    dTdotdC_sym = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    #need to do some trickery here to get the right derivative
    #due to weirdness with differentiation of indxedfunc's
    num, den = fraction(dTdt)

    omega_k = Function(r'\dot{\omega}_k')(Ck, T, k)

    num = Sum(omega_k * h[k], (k, 1, Ns))
    dTdt_new = num / den
    write_eq(diff(T, t), dTdt_new)

    dTdotdC = diff(dTdt_new, Ck[i])
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
            num = num.subs(subs_term_num, CkCpSum).subs(
                subs_term_den, CkCpSum)
            den = den.subs(subs_term_num, CkCpSum).subs(
                subs_term_den, CkCpSum)
            subs_terms.append(num / den)

        return Add(*subs_terms)

    dTdotdC = __collapse_cp_conc_sum(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)

    #another level of compactness, replaces the kronecker delta sum
    num, den = fraction(dTdotdC)
    num_terms = Add.make_args(num)
    kd_term = next(x for x in num_terms if x.has(KroneckerDelta))
    num_terms = Add(*[x for x in num_terms if x != kd_term])
    kd_term = kd_term.subs(Sum((cp[Ns] - cp[k]) * KroneckerDelta(k, i), (k, 1, Ns - 1)),
        (cp[Ns] - cp[i]))
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
        expr = expr.subs(omega_k, omega_sym[k])

        num, den = fraction(expr)
        out_terms = []
        add_terms = Add.make_args(num)
        for term in add_terms:
            if term.has(Ck[k]) and term.has(cp[k]) and term.has(omega_sym[k])\
                and term.has(h[k]) and term.has(Sum):
                #this is the one
                assert isinstance(term, Mul)
                subterms = Mul.make_args(term)
                out_sub_terms = []
                for sterm in subterms:
                    n, d = fraction(sterm)
                    if d == CkCpSum:
                        continue
                    elif n == Sum(omega_sym[k] * h[k], (k, 1, Ns)):
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

    #now we factor out the Ck cp sum
    dTdotdT = factor_terms(dTdotdT, CkCpSum)
    write_eq(dTdotdT_sym, dTdotdT)

    #and replace the dTdt term
    dTdotdT = __rep_dT_dt(dTdotdT)
    write_eq(dTdotdT_sym, dTdotdT)

    #the final simplification is of the [C]cp[ns] term
    dTdotdT = dTdotdT.subs(Ctot_sym * diff(cp[Ns], T), diff(cp[Ns], T) * Sum(Ck[k], (k, 1, Ns)))
    write_eq(dTdotdT_sym, dTdotdT)

    num, den = fraction(dTdotdT)
    #seach for the Ck sums
    add_terms = Add.make_args(num)
    simp_term = next(x for x in add_terms if x.has(Sum) and x.has(Ck[k]))
    add_terms = [x for x in add_terms if x != simp_term]
    to_simp = Mul.make_args(simp_term)
    constant = Mul(*[x for x in to_simp if not (x.has(Ck[k]) and x.has(Sum))])
    to_simp = next(x for x in to_simp if not constant.has(x))
    #we now have the Ck sum

    #make sure it's the right thing
    check_term = -diff(cp[Ns], T) * Sum(Ck[k], (k, 1, Ns))\
        + Sum((diff(cp[Ns], T) - diff(cp[k], T)) * Ck[k], (k, 1, Ns - 1))
    other_add = Ctot_sym * cp[Ns] / T
    assert simplify(to_simp - (check_term + other_add)) == 0

    #make the replacement term
    rep_term = -diff(cp[Ns], T) * Sum(Ck[k], (k, 1, Ns - 1)) + -diff(cp[Ns], T) * Ck[Ns] +\
                    Sum((diff(cp[Ns], T) - diff(cp[k], T)) * Ck[k], (k, 1, Ns - 1))
    assert simplify(rep_term - (-Sum(diff(cp[k], T) * Ck[k], (k, 1, Ns - 1)) 
                - diff(cp[Ns], T) * Ck[Ns])) == 0

    #and reconstruct
    add_terms.append(constant * (-Sum(Ck[k] * diff(cp[k], T), (k, 1, Ns)) + 
        other_add))
    dTdotdT = Add(*add_terms) / den
    write_eq(dTdotdT_sym, dTdotdT)

    return

    #concentration Jacobian equations
    dCdot = IndexedFunc(r'\dot{C}', (Ck[k], T))
    write_eq(Eq(diff(dCdot[k], Ck[i]), simplify(diff(omega, Ck[k]))))
    write_eq(Eq(diff(dCdot[k], T), simplify(diff(omega, T))))


if __name__ == '__main__':
    class filer(object):
        def __init__(self, name, mode):
            import re
            self.name = os.path.join(out_dir, name)
            self.mode = mode
            self.lines = [r'\documentclass[a4paper,10pt]{article}' + '\n' +
                           r'\usepackage[utf8]{inputenc}' + '\n'
                           r'\usepackage{amsmath}' + '\n' +
                           r'\usepackage{breqn}' + '\n' + 
                           r'\begin{document}' + '\n']
            self.regex = re.compile('{equation}')

        def __enter__(self):
            return self

        def write(self, thestr):
            self.lines.append(thestr)
        def __exit__(self, type, value, traceback):
            self.write(r'\end{document}' + '\n')
            self.lines = [self.regex.sub(r'{dmath} ', line) for line in self.lines]
            with open(self.name, self.mode) as file:
                file.writelines(self.lines)

    with filer('thermo_derivation.tex', 'w') as file:
        thermo_derivation(IndexedBase('Y'), file)

    with filer('conp_derivation.tex', 'w') as file:
        conp_derivation(file)
    