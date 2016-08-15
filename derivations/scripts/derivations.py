from sympy.interactive.printing import init_printing
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
from sympy.functions.special.polynomials import chebyshevt, chebyshevu
from sympy.core.numbers import Rational, Float
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

class MyImplicitSymbol(ImplicitSymbol):
    def _get_df(self, arg, wrt):
        if isinstance(arg, IndexedConc) and \
                    isinstance(wrt, MyIndexedFunc.MyIndexedFuncValue) and \
                    isinstance(wrt.base, IndexedConc):
            return MyImplicitSymbol(self.base_str.format(
                    str(self.name), str(wrt)), args=self.functional_form)
        return MyImplicitSymbol(self.base_str.format(
                str(self.name), str(arg)), args=self.functional_form)

class MyIndexedFunc(IndexedFunc):
    class MyIndexedFuncValue(IndexedFunc.IndexedFuncValue):
        def _get_df(self, arg, wrt):
            if isinstance(arg, IndexedConc) and \
                    isinstance(wrt, MyIndexedFunc.MyIndexedFuncValue) and \
                    isinstance(wrt.base, IndexedConc):
                return MyIndexedFunc(self.base_str.format(
                        str(self.base), str(wrt)), args=self.functional_form)[self.indices]
            return MyIndexedFunc(self.base_str.format(
                        str(self.base), str(arg)), args=self.functional_form)[self.indices]

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
            if self.shape and len(self.shape) != len(indices):
                raise IndexException("Rank mismatch.")
            return MyIndexedFunc.MyIndexedFuncValue(self,
                self.functional_form,
                *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return MyIndexedFunc.MyIndexedFuncValue(self,
                self.functional_form,
                indices, **kw_args)



#some custom behaviour for concentrations
class IndexedConc(MyIndexedFunc):
    is_Real = True
    is_Positive = True
    is_Negative = False
    is_Number = True
    _diff_wrt = True
    def _eval_derivative(self, wrt):
        if isinstance(wrt, MyIndexedFunc.MyIndexedFuncValue) and \
            isinstance(wrt.base, IndexedConc):
            return S.One
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

def write_section(title, **kw_args):
    writer = file if not 'myfile' in kw_args else kw_args['myfile']
    writer.write(r'\section{{{}}}'.format(title) + '\n')

"""
ConP / ConV independent symbols
"""

#time
t = symbols('t', float=True, finite=True, negative=False, real=True)


#thermo vars
T = MyImplicitSymbol('T', t)  

#mechanism size
Ns = S.Ns
Nr = S.Nr

#index variables
k = Idx('k', (1, Ns + 1))
i = Idx('i', (1, Nr + 1))
j = Idx('j')
l = Idx('l')
m = Idx('m')

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
    cp = MyIndexedFunc(r'{C_p}', T)
    cp_mass = MyIndexedFunc(r'{c_p}', T)

    cp_tot_sym = MyImplicitSymbol(r'\bar{c_p}', T,)
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
    h = MyIndexedFunc(r'H', T)
    h_mass = MyIndexedFunc(r'h', T)

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
    s = MyIndexedFunc(r'S', T)
    if subfile:
        write(Eq(Eq(Symbol(r'S_k^{\circ}'), s[k]), Sfunc), 
            expand(Sfunc))

    Bk = simplify(Sfunc / R - hfunc / (R * T))

    return cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass, Bk

def reaction_derivation(P, Ck, Ctot_sym, Bk, subfile):
    def write(*args):
        write_eq(*args, myfile=subfile)
    def write_dummy(*args):
        write_dummy_eq(*args, myfile=subfile)
    def write_sec(*args):
        write_section(*args, myfile=subfile)
    nu_f = IndexedBase(r'\nu^{\prime}')
    nu_r = IndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[k, i] - nu_r[k, i]
    nu_sym = IndexedBase(r'\nu')
    write(nu_sym[k, i], nu)

    #define for later use
    Ctot = P / (R * T)
    Cns = Ctot - Sum(Ck[k], (k, 1, Ns - 1))
    Cns_sym = ImplicitSymbol('[C]_{Ns}', Cns)
    write(Ck[Ns], Cns)

    omega_sym = MyIndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck, T, nu, P))
    write(diff(Ck[k], t), omega_sym[k])

    q = MyIndexedFunc('q', args=(Ck, T, P))
    omega_k = Sum(nu_sym[k, i] * q[i], (i, 1, Nr))
    write(omega_sym[k], omega_k)

    Rop_sym = MyIndexedFunc('R', args=(Ck, T))
    ci = MyIndexedFunc('c', args=(Ck, P, T))

    write(q[i], Rop_sym[i] * ci[i])

    #arrhenius coeffs
    A = IndexedBase(r'A')
    Beta = IndexedBase(r'\beta')
    Ea = IndexedBase(r'{E_{a}}')

    write_sec('Rate of Progress')
    Ropf_sym = MyIndexedFunc(r'{R_f}', args=(Ck, T))
    Ropr_sym = MyIndexedFunc(r'{R_r}', args=(Ck, T))

    Rop = Ropf_sym[i] - Ropr_sym[i]
    write(Rop_sym[i], Ropf_sym[i] - Ropr_sym[i])
    
    kf_sym = MyIndexedFunc(r'{k_f}', T)
    Ropf = kf_sym[i] * Product(Ck[k]**nu_f[k, i], (k, 1, Ns))
    write(Ropf_sym[i], Ropf)

    kr_sym = MyIndexedFunc(r'{k_r}', T)
    Ropr = kr_sym[i] * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write(Ropr_sym[i], Ropr)

    write_sec('Pressure Dependent Forms')
    #write the various ci forms
    ci_elem = 1
    write_dummy('c_{{i}} = {}'.format(ci_elem) + r'\text{\quad for elementary reactions}')

    ci_thd_sym = MyImplicitSymbol('[X]_i', args=(Ck, T, P))
    write_dummy('c_{{i}} = {}'.format(latex(ci_thd_sym)) + r'\text{\quad for third-body enhanced reactions}')

    Pri_sym = MyImplicitSymbol('P_{r, i}', args=(T, Ck, P))
    Fi_sym = MyImplicitSymbol('F_{i}', args=(T, Ck, P))
    ci_fall = (Pri_sym / (1 + Pri_sym)) * Fi_sym
    write_dummy(latex(Eq(ci[i], ci_fall)) + r'\text{\quad for unimolecular/recombination falloff reactions}')

    ci_chem = (1 / (1 + Pri_sym)) * Fi_sym  
    write_dummy(latex(Eq(ci[i], ci_chem)) + r'\text{\quad for chemically-activated bimolecular reactions}')

    write_sec('Forward Reaction Rate')
    kf = A[i] * (T**Beta[i]) * exp(-Ea[i] / (R * T))
    write(kf_sym[i], kf)

    
    write_sec('Equilibrium Constants')
    Kp_sym = MyIndexedFunc(r'{K_p}', args=(T, a))
    Kc_sym = MyIndexedFunc(r'{K_c}', args=(T))
    write(Kc_sym[i], Kp_sym[i] * ((Patm / (R * T))**Sum(nu_sym[k, i], (k, 1, Ns))))

    write_dummy(latex(Kp_sym[i]) + ' = ' + 
        r'\text{exp}(\frac{\Delta S^{\circ}_k}{R_u} - \frac{\Delta H^{\circ}_k}{R_u T})')
    write_dummy(latex(Kp_sym[i]) + ' = ' + 
        r'\text{exp}(\sum_{k=1}^{N_s}\frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T})')

    B_sym = MyIndexedFunc('B', T)
    Kc = ((Patm / R)**Sum(nu_sym[k, i], (k, 1, Ns))) * exp(Sum(nu_sym[k, i] * B_sym[k], (k, 1, Ns)))
    write(Kc_sym[i], Kc)

    write_dummy(latex(B_sym[k]) + r'= \frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T} - ln(T)')

    Bk = Bk - log(T)
    Bk_rep = a[k, 6] - a[k, 0] + (a[k, 0] - 1)*log(T) +\
        T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 6) + T * \
            (a[k, 3] * Rational(1, 12) + a[k, 4] * T * Rational(1, 20)))) - \
        a[k, 5] / T

    assert simplify(Bk - Bk_rep) == 0
    write(B_sym[k], Bk_rep)

    write_sec('Reverse Reaction Rate')
    kr = kf / Kc
    kr_sym = MyIndexedFunc(r'{k_r}', args=(T))
    write(kr_sym[i], kf_sym[i] / Kc_sym[i])
    
    write_sec('Third Body Efficiencies')
    thd_bdy_eff = IndexedBase(r'\alpha')
    ci_thd = Sum(thd_bdy_eff[k, i] * Ck[k], (k, 1, Ns))
    write(ci_thd_sym, ci_thd)
    ci_thd = Ctot_sym - Sum((S.One - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns))
    write(ci_thd_sym, ci_thd)
    ci_thd = ci_thd.subs(Ctot_sym, Ctot).subs(
        Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns)),
        Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns - 1)) + 
        (1 - thd_bdy_eff[Ns, i]) * Cns)
    write(ci_thd_sym, ci_thd)
    ci_thd = factor_terms(simplify(ci_thd), Ck[k]).subs(Ctot, Ctot_sym)

    write(ci_thd_sym, ci_thd)

    write_dummy(latex(Eq(ci_thd_sym, Ck[m])) + r'\text{\quad for a single species third body}') 

    write_sec('Falloff Reactions')
    k0 = Symbol('A_0') * T**Symbol(r'\beta_0') * exp(-Symbol('E_{a, 0}') / (R * T))
    kinf = Symbol(r'A_{\infty}') * T**Symbol(r'\beta_{\infty}') * exp(-Symbol(r'E_{a, \infty}') / (R * T))
    k0_sym = MyImplicitSymbol(r'k_{0, i}', T)
    kinf_sym = MyImplicitSymbol(r'k_{\infty, i}', T)
    Pri_mix = ci_thd_sym  * k0_sym / kinf_sym
    write_dummy(latex(Eq(Pri_sym, Pri_mix)) + r'\text{\quad for the mixture as the third body}')
    Pri_spec = Ck[m] * k0_sym / kinf_sym
    write_dummy(latex(Eq(Pri_sym, Pri_spec)) + r'\text{\quad for species $m$ as the third body}')

    Fi_lind = 1
    write_dummy(latex(Eq(Fi_sym, Fi_lind)) + r'\text{\quad for Lindemann}')

    Fcent_sym = MyImplicitSymbol('F_{cent}', T)
    Atroe_sym = MyImplicitSymbol('A_{Troe}', args=(Pri_sym, Fcent_sym))
    Btroe_sym = MyImplicitSymbol('B_{Troe}', args=(Pri_sym, Fcent_sym))
    Fcent_power = (1 + (Atroe_sym / Btroe_sym)**2)**-1
    Fi_troe = Fcent_sym**Fcent_power
    Fi_troe_sym = ImplicitSymbol('F_{i}', args=(Fcent_sym, Pri_sym))
    write_dummy(latex(Eq(Fi_sym, Fi_troe)) + r'\text{\quad for Troe}')

    X_sym = MyImplicitSymbol('X', Pri_sym)
    a_fall, b_fall, c_fall, d_fall, e_fall, \
        Tstar, Tstarstar, Tstarstarstar = symbols('a b c d e T^{*} T^{**} T^{***}')
    Fi_sri = d_fall * T ** e_fall * (
        a_fall * exp(-b_fall / T) + exp(-T / c_fall))**X_sym
    write_dummy(latex(Eq(Fi_sym, Fi_sri)) + r'\text{\quad for SRI}')

    Fcent = (S.One - a_fall) * exp(-T / Tstarstarstar) + a_fall * exp(-T / Tstar) + \
        exp(-Tstarstar / T)
    write(Fcent_sym, Fcent)

    Atroe = log(Pri_sym, 10) - Float(0.67) * log(Fcent_sym, 10) - Float(0.4)
    write(Atroe_sym, Atroe)

    Btroe = Float(0.806) - Float(1.1762) * log(Fcent_sym, 10) - Float(0.14) * log(Pri_sym, 10)
    write(Btroe_sym, Btroe)

    X = (1 + (log(Pri_sym, 10))**2)**-1
    write(X_sym, X)

    write_sec('Pressure-dependent Reactions')

    #pdep
    subfile.write('For PLog reactions\n')
    k1 = Symbol('A_1') * T**Symbol(r'\beta_1') * exp(-Symbol('E_{a, 1}') / (R * T))
    k2 = Symbol('A_2') * T**Symbol(r'\beta_2') * exp(-Symbol('E_{a, 2}') / (R * T))
    k1_sym = MyImplicitSymbol('k_1', T)
    k2_sym = MyImplicitSymbol('k_2', T)
    write_dummy(latex(Eq(k1_sym, k1)) + r'\text{\quad at } P_1')
    write_dummy(latex(Eq(k2_sym, k2)) + r'\text{\quad at } P_2')

    kf_pdep = log(k1_sym, 10) + (log(k2_sym, 10) - log(k1_sym, 10)) * (log(P) - log(Symbol('P_1'))) / (log(Symbol('P_2')) - log(Symbol('P_1')))
    kf_pdep_sym = Function('k_f')(T, P)
    write(log(kf_pdep_sym, 10), kf_pdep)

    #cheb
    subfile.write('For Chebyshev reactions\n')
    Tmin, Tmax, Pmin, Pmax = symbols('T_{min} T_{max} P_{min} P_{max}')
    Tred = (2 * T**-1 - Tmin**-1 - Tmax**-1) / (Tmax**-1 - Tmin**-1) 
    Pred = (2 * log(P, 10) - log(Pmin, 10) - log(Pmax, 10)) / (log(Pmax, 10) - log(Pmin, 10))
    Tred_sym = MyImplicitSymbol(r'\tilde{T}', Tred)
    Pred_sym = MyImplicitSymbol(r'\tilde{P}', Pred)

    Nt, Np = symbols('N_T N_P')
    eta = IndexedBase(r'\eta')
    kf_cheb = Sum(Sum(eta[i, j] * chebyshevt(m - 1, Tred_sym) * chebyshevt(j - 1, Pred_sym), 
        (j, 1, Np)), (m, 1, Nt))
    kf_cheb_sym = Function('k_f')(T, P)
    write(log(kf_cheb_sym, 10), kf_cheb)

    write_sec('Derivatives')
    write(diff(omega_sym[k], T), diff(omega_k, T))
    write(diff(q[i], T), diff(Rop_sym[i] * ci[i], T))

    write(diff(omega_sym[k], Ck[k]), diff(omega_k, Ck[j]))
    write(diff(q[i], Ck[k]), diff(Rop_sym[i] * ci[i], Ck[j]))

    write_sec('Rate of Progress Derivatives')
    write(diff(Ropf_sym, T), diff(Ropf, T))
    write(diff(Ropf_sym, Ck[k]), diff(Ropf, Ck[j]))

    write_dummy(r'\frac{\partial [C_k]}{\partial [C_j]} =' + latex(
        diff(Ck[k], Ck[j])))
    write_dummy(r'\frac{\partial [C_{Ns}]}{\partial [C_j]} =' + latex(
        Eq(diff(Cns, Ck[j]), -S.One)))

    dCnsdCj = diff(Cns**nu_f[k, i], Ck[j])
    write_dummy(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{k, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj))
    dCnsdCj = simplify(dCnsdCj.subs(Cns, Cns_sym).subs(Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1))
    write_dummy(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{k, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj))

    def __mod_prod_sum(kval, fwd=True):
        nuv = nu_f if fwd else nu_r
        if kval == Ns:
            return Product(Ck[l]**nuv[l, i], (l, 1, Ns - 1))
        else:
            return Product(Ck[l]**nuv[l, i], (l, 1, k - 1), (l, k + 1, Ns))

    dRopfdCj = Sum(nu_f[k, i] * Ck[k] ** (nu_f[k, i] - 1) * 
        __mod_prod_sum(k), (k, 1, Ns - 1)) - \
        nu_f[Ns, i] * Ck[Ns]**(nu_f[Ns, i] - 1) * __mod_prod_sum(Ns)
    write(diff(Ropf / kf_sym[i], Ck[j]), dRopfdCj)

    def __create_dRopdCj(fwd=True):
        nuv = nu_f if fwd else nu_r
        krate = kf_sym[i] if fwd else kr_sym[i]
        return krate * Sum((1 - 2 * KroneckerDelta(k, Ns)) * nuv[k, i] * Ck[k] ** (nuv[k, i] - 1) * 
        __mod_prod_sum(k, fwd), (k, 1, Ns))

    dRopfdCj = __create_dRopdCj()
    write(diff(Ropf_sym[i], Ck[j]), dRopfdCj)

    dRoprdCj = __create_dRopdCj(False)
    write(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    dkfdT = factor_terms(diff(kf, T), kf).subs(kf, kf_sym[i])
    write(diff(kf_sym[i], T), dkfdT)

    dRopfdT = diff(Ropf, T).subs(diff(kf_sym[i], T), dkfdT).subs(
        Ropf, Ropf_sym[i])
    write(diff(Ropf_sym[i], T), dRopfdT)

    subfile.write('For reactions with explicit reverse Arrhenius coefficients\n')

    A_rexp = IndexedBase(r'{A_{r}}')
    Beta_rexp = IndexedBase(r'{\beta_r}')
    Ea_rexp = IndexedBase(r'{E_{a,r}}')
    kr_rexp = A_rexp[i] * T**Beta_rexp[i] * exp(-Ea_rexp[i] / (R * T))
    Ropr_rexp = kr_rexp * Product(Ck[l]**nu_r[k, i], (k, 1, Ns))
    dRopr_rexpdT =  diff(Ropr_rexp, T)
    dRopr_rexpdT = factor_terms(dRopr_rexpdT, Ropr_rexp / T).subs(Ropr_rexp, Ropr_sym[i])
    dRop_expdT = dRopfdT - dRopr_rexpdT
    dRop_expdT = dRop_expdT.subs(Ropf, Ropf_sym[i])

    write(diff(Rop_sym[i], T), dRop_expdT)

    subfile.write('For non-explicit reversible reactions\n')
    dkrdT = diff(kf_sym[i] / Kc_sym[i], T)
    write(diff(kr_sym[i], T), dkrdT)
    dkrdT = dkrdT.subs(diff(kf_sym[i], T), dkfdT)
    dkrdT = dkrdT.subs(kf_sym[i] / Kc_sym[i], kr_sym[i])
    dkrdT = factor_terms(dkrdT, kr_sym[i])
    write(diff(kr_sym[i], T), dkrdT)

    #dkcdT
    dKcdT = diff(Kc, T)
    dKcdT = dKcdT.subs(Kc, Kc_sym[i])
    write(diff(Kc_sym[i], T), dKcdT)

    #sub into dkrdT
    dkrdT = dkrdT.subs(diff(Kc_sym[i], T), dKcdT)
    write(diff(kr_sym[i], T), dkrdT)

    #now the full dRdT
    dRoprdT = diff(Ropr, T).subs(diff(kr_sym[i], T), dkrdT)
    dRoprdT = dRoprdT.subs(Ropr, Ropr_sym[i])
    write(diff(Ropr_sym[i], T), dRoprdT)

    dRopdT = diff(Rop, T).subs(diff(Ropf_sym[i], T),
        dRopfdT).subs(diff(Ropr_sym[i], T), dRoprdT)
    write(diff(Rop_sym[i], T), dRopdT)

    subfile.write('For all reversible reactions\n')
    #now do dRop/dCj
    dRopdCj = diff(Rop, Ck[j]).subs(diff(Ropf_sym[i], Ck[j]),
        dRopfdCj).subs(diff(Ropr_sym[i], Ck[j]), dRoprdCj)
    write(diff(Rop_sym[i], Ck[j]), dRopdCj)

    write_sec(r'Third-Body\slash Pressure-Depencence Derivatives')
    subfile.write('For elementary reactions\n')
    write(diff(ci[i], T), diff(ci_elem, T))
    write(diff(ci[i], Ck[j]), diff(ci_elem, Ck[j]))

    subfile.write('For third body enhanced reactions\n')
    dci_thddT = diff(ci_thd.subs(Ctot_sym, Ctot), T).subs(
        Ctot, Ctot_sym)
    write(diff(ci_thd_sym, T), dci_thddT)
    dci_thddCj = diff(ci_thd.subs(Ctot_sym, Ctot), Ck[j])
    dci_thddCj = dci_thddCj.subs(Sum((thd_bdy_eff[Ns, i] - thd_bdy_eff[k, i]) *
        KroneckerDelta(j, k), (k, 1, Ns - 1)), thd_bdy_eff[Ns, i] - thd_bdy_eff[j, i])
    write(diff(ci_thd_sym, Ck[j]), dci_thddCj)

    subfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    dci_unity_dCj = diff(Ctot, Ck[j])
    write(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)

    subfile.write('For unimolecular/recombination fall-off reactions\n')
    dci_falldT = collect(diff(ci_fall, T).subs(ci_fall, ci[i]), diff(Pri_sym, T))
    write(diff(ci[i], T), dci_falldT)

    dci_falldCj = collect(diff(ci_fall, Ck[j]).subs(ci_fall, ci[i]), diff(Pri_sym, Ck[j]) / 
        (Pri_sym + 1))
    write(diff(ci[i], Ck[j]), dci_falldCj)

    subfile.write('For chemically-activated bimolecular reactions\n')
    dci_chemdT = collect(diff(ci_chem, T).subs(ci_chem, ci[i]), diff(Pri_sym, T))
    write(diff(ci[i], T), dci_chemdT)

    dci_chemdCj = collect(diff(ci_chem, Ck[j]).subs(ci_chem, ci[i]), diff(Pri_sym, Ck[j]) / 
        (Pri_sym + 1))
    write(diff(ci[i], Ck[j]), dci_chemdCj)

    subfile.write('The $P_{r, i}$ derivatives are:\n')
    dPri_mixdT = diff(Pri_mix, T).subs(diff(ci_thd_sym, T), dci_thddT)
    dkinfdT = dkfdT.subs([(A[i], Symbol(r'A_{\infty}')),
        (Beta[i], Symbol(r'\beta_{\infty}')), (Ea[i], Symbol(r'E_{a, \infty}')),
        (kf_sym[i], kinf_sym)])
    dk0dT = dkfdT.subs([(A[i], Symbol(r'A_{0}')),
        (Beta[i], Symbol(r'\beta_{0}')), (Ea[i], Symbol(r'E_{a, 0}')),
        (kf_sym[i], k0_sym)])

    dPri_mixdT = dPri_mixdT.subs([(diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT)])
    dPri_mixdT = collect(dPri_mixdT, Pri_mix / T).subs(Pri_mix, Pri_sym)

    subfile.write('\nFor the mixture as the third body\n')
    write(diff(Pri_sym, T), dPri_mixdT)

    dPri_mixdCj = diff(Pri_mix, Ck[j]).subs(diff(ci_thd_sym, Ck[j]), dci_thddCj)
    write(diff(Pri_sym, Ck[j]), dPri_mixdCj)

    subfile.write('For species $m$ as the third body\n')

    dPri_specdT = diff(Pri_spec, T)
    dPri_specdT = dPri_specdT.subs([(diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT)])
    dPri_specdT = collect(dPri_specdT, Pri_spec / T).subs(Pri_spec, Pri_sym)
    write(diff(Pri_sym, T), dPri_specdT)

    dCmdCj = diff(Ck[m], Ck[j]) - diff(Ck[m], Ck[Ns])
    dPri_specdCj = diff(Pri_spec, Ck[j]).subs(diff(Ck[m], Ck[j]), dCmdCj)
    write(diff(Pri_sym, Ck[j]), dPri_specdCj)

    subfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    Pri_unity = Pri_mix.subs(ci_thd_sym, Ctot)
    Pri_unity_sym = Pri_unity.subs(Ctot, Ctot_sym)
    dPri_unitydT = diff(Pri_unity, T).subs(Ctot, Ctot_sym)
    dPri_unitydT = dPri_unitydT.subs([(diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT)])

    dPri_unitydT = collect(dPri_unitydT, Pri_unity_sym / T).subs(Pri_unity_sym, Pri_sym)
    write(diff(Pri_sym, T), dPri_unitydT)

    dPri_unitydCj = diff(Pri_unity, Ck[j])
    write(diff(Pri_sym, Ck[j]), dPri_unitydCj)

    subfile.write('The $F_i$ derivatives are:\n')
    subfile.write('\n For Lindemann reactions\n')

    dFi_linddT = diff(Fi_lind, T)
    dFi_linddCj = diff(Fi_lind, Ck[j])
    write(diff(Fi_sym, T), dFi_linddT)
    write(diff(Fi_sym, Ck[j]), dFi_linddCj)
    
    subfile.write('For Troe reactions\n')
    dFi_troedT = diff(Fi_troe_sym, T)
    dFi_troedCj = diff(Fi_troe_sym, Ck[j])
    write(diff(Fi_sym, T), dFi_troedT)
    write(diff(Fi_sym, Ck[j]), dFi_troedCj)

    subfile.write('where\n')
    troe_collect_poly = 2 * Atroe_sym / (Btroe_sym**3)
    dFi_troedFcent = factor_terms(
        diff(Fi_troe, Fcent_sym).subs(Fi_troe, Fi_troe_sym),
        Fi_troe_sym / Fcent_power)
    dFcentdT = diff(Fcent, T)
    write(diff(Fcent_sym, T), dFcentdT)
    write(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)
    dFi_troedPri = factor_terms(
        diff(Fi_troe, Pri_sym).subs(Fi_troe, Fi_troe_sym),
        troe_collect_poly)
    write(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    subfile.write('And\n')
    dAtroedFcent = diff(Atroe, Fcent_sym)
    dBtroedFcent = diff(Btroe, Fcent_sym)
    dAtroedPri = diff(Atroe, Pri_sym)
    dBtroedPri = diff(Btroe, Pri_sym)
    write(diff(Atroe_sym, Fcent_sym), dAtroedFcent)
    write(diff(Btroe_sym, Fcent_sym), dBtroedFcent)
    write(diff(Atroe_sym, Pri_sym), dAtroedPri)
    write(diff(Btroe_sym, Pri_sym), dBtroedPri)


    subfile.write('For SRI reactions\n')
    dFi_sridT = factor_terms(diff(Fi_sri, T).subs(Fi_sri, Fi_sym), Fi_sym)
    dFi_sridCj = diff(Fi_sri, Ck[j]).subs(Fi_sri, Fi_sym)
    write(diff(Fi_sym, T), dFi_sridT)
    write(diff(Fi_sym, Ck[j]), dFi_sridCj)

    subfile.write('Where\n')
    dXdPri = diff(X, Pri_sym).subs(X, X_sym)
    write(diff(X_sym, Pri_sym), dXdPri)
    write_dummy(r'\frac{\partial X}{\partial [C]_j} = ' + latex(diff(X_sym, Ck[j])))

    write_sec('Pressure-dependent reaction derivatives')
    subfile.write('For PLog reactions\n')
    dkf_pdepdT = diff(kf_pdep, T)
    write(diff(kf_sym[i], T), dkf_pdepdT)
    #easier to redo with substituted vals
    dkf_pdepdT = diff(kf_pdep.subs([(k1_sym, k1), (k2_sym, k2)]), T)
    write(diff(kf_sym[i], T), dkf_pdepdT)
    #now want to collapse back
    dkf_pdepdT = collect(dkf_pdepdT, k1)
    dkf_pdepdT = dkf_pdepdT.subs([(log(k1), log(k1_sym)), (log(k2), log(k2_sym))])
    write(diff(kf_sym[i], T), dkf_pdepdT)
    #and even futher
    dkf_pdepdT = factor_terms(dkf_pdepdT.subs(kf_pdep, kf_pdep_sym), kf_pdep_sym / T)
    write(diff(kf_sym[i], T), dkf_pdepdT)
    
    return nu_sym, nu, omega_sym, omega_k, q, Rop_sym, ci



def conp_derivation(file):
    #thermo vars
    Ck = IndexedConc('[C]', t)

    #define concentration
    P = S.pressure
    V_sym = MyImplicitSymbol('V', t)
    V = V_sym
    state_vec = [T, Ck[1], Ck[2], Ck[Ns]]

    #define state vector
    state_vec_str = ' = ' + r'\left\{{{}\ldots {}\right\}}'
    state = MyImplicitSymbol(r'\Phi', t)
    write_dummy_eq(str(state) + state_vec_str.format(
        ','.join([str(x) for x in state_vec[:-1]]),
        str(state_vec[-1])))

    write_dummy_eq(str(diff(state, t)) + state_vec_str.format(
        ','.join([str(diff(x, t)) for x in state_vec[:-1]]),
        str(diff(state_vec[-1], t))))

    n_sym = MyImplicitSymbol('n', t)
    n = P * V / (R * T)
    write_eq(n_sym, n)

    Ctot_sym = MyImplicitSymbol('[C]', T)
    Ctot = P / (R * T)
    write_eq(Ctot_sym, Ctot)
    Cns_sym = MyImplicitSymbol('[C]_{N_s}', args=(P, T))
    Cns = Ctot - Sum(Ck[k], (k, 1 , Ns - 1))
    write_eq(Cns_sym, Cns)

    #molecular weight
    Cns_simp = 1 - Sum(Ck[k], (k, 1 , Ns - 1)) / Ctot
    assert expand(Cns / Ctot) - expand(Cns_simp) == 0
    W = Sum(Wi[k] * Ck[k], (k, 1, Ns - 1)) / Ctot_sym + Wi[Ns] * Cns_simp.subs(1 / Ctot, 1 / Ctot_sym)
    W_new = Wi[Ns] + Sum(Ck[k] * (Wi[k] - Wi[Ns]), (k, 1, Ns - 1)) / Ctot_sym
    assert simplify(W - W_new) == 0
    W = W_new
    
    W_sym = MyImplicitSymbol('W', t)
    write_eq(W_sym, W)

    m = n * W
    density = m / V
    density_sym = MyImplicitSymbol(r'\rho', t)
    write_eq(density_sym, n_sym * W_sym / V_sym)

    #mass fractions
    Yi_sym = MyIndexedFunc('Y', args=(density, Ck[k], Wi[k]))
    Yi = Ck[k] * Wi[k]/ density_sym

    write_eq(Yi_sym[k], Yi)

    #get all our thermo symbols
    cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass, Bk = thermo_derivation(Yi)

    #reaction rates

    with filer('conp_reaction_derivation.tex', 'w') as subfile:
        reaction_derivation(P, Ck, Ctot_sym, Bk, subfile)

    return

    #rate of progress
    rop = kf_sym[i] * Product(Ck[k]**nu_f[k, i], (k, 1, Ns)) - kr_sym * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    rop_sym = MyIndexedFunc(r'{R_{net}}', args=(Ck, T, nu))

    write_eq(Eq(rop_sym[i], rop))
    
    #net reaction rate
    omega = Sum(rop, (i, 1, Nr))
    omega_sym = MyIndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck[k], T, nu))

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
    dCdot = MyIndexedFunc(r'\dot{C}', (Ck[k], T))
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
    