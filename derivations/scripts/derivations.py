from sympy.interactive.printing import init_printing
from sympy.simplify.radsimp import collect, fraction
from sympy.simplify.simplify import simplify, cancel, separatevars, sum_simplify, signsimp
from sympy.simplify.ratsimp import ratsimp
from sympy.solvers.solvers import solve
from sympy.core.symbol import symbols, Symbol, Wild
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
    def _print_ExpBase(self, expr, exp=None):
        tex = r"\operatorname{exp}\left({%s}\right)" % self._print(expr.args[0])
        return self._do_exponent(tex, exp)

#override default latex print method
def latex(expr, **settings):
    return CustomLatexPrinter(settings).doprint(expr)

class MyImplicitSymbol(ImplicitSymbol):
    def _get_df(self, arg, wrt):
        if isinstance(arg, IndexedConc) and \
                    isinstance(wrt, MyIndexedFunc.MyIndexedFuncValue) and \
                    isinstance(wrt.base, IndexedConc):
            return self.__class__(self.base_str.format(
                    str(self.name), str(wrt)), args=self.functional_form)
        return self.__class__(self.base_str.format(
                str(self.name), str(arg)), args=self.functional_form)

class MyIndexedFunc(IndexedFunc):
    def _get_subclass(self, *args):
        return MyIndexedFunc.MyIndexedFuncValue(*args)

    class MyIndexedFuncValue(IndexedFunc.IndexedFuncValue):
        def _get_df(self, arg, wrt):
            if isinstance(arg, IndexedConc) and \
                    isinstance(wrt, MyIndexedFunc.MyIndexedFuncValue) and \
                    isinstance(wrt.base, IndexedConc):
                return self.base.__class__(self.base_str.format(
                        str(self.base), str(wrt)), self.functional_form)[self.indices]
            return super(MyIndexedFunc.MyIndexedFuncValue, self)._get_df(arg, wrt)



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

equivalences = {}
def register_equal(v1, v2=None):
    def __add(v1, v2):
        if v1 not in equivalences:
            equivalences[v1] = [v2]
        else:
            equivalences[v1].append(v2)
    if isinstance(v1, list) and v2 is None:
        for vv1, vv2 in v1:
            __add(vv1, vv2)
    else:
        assert v2 is not None
        __add(v1, v2)


def assert_subs(obj, *subs_args, **kw_args):
    """
    A helper method to ensure that all 'subs' operations
    do not substitute non-equivalent values

    If assumptions is not None, a list of simplifying assumptions to be used
    are supplied
    """

    def test_equal(v1, v2):
        def __rep_dummy_sum(arg):
            out_terms = []
            for term in Mul.make_args(arg):
                if isinstance(term, Sum) and term.limits[0][1] == term.limits[0][2]:
                    out_terms.append(term.function.subs(term.limits[0][0], term.limits[0][1]))
                else:
                    out_terms.append(term)
            return Mul(*out_terms)
        #weed out dummy sums
        v1 = __rep_dummy_sum(v1)
        v2 = __rep_dummy_sum(v2)

        if v1 == v2:
            return True

        #special cases
        #kronecker delta collapses
        if v1.has(KroneckerDelta) and isinstance(v1, Sum):
            #get the KD term
            func = v1.function
            args = Mul.make_args(factor_terms(func))
            KD = next((x for x in args if isinstance(x, KroneckerDelta)), None)
            #check that the substitution is formatted as we thought
            assert KD is not None
            #and that the KD includes the summation variable
            sum_var = next(v for v in KD.args if v == v1.limits[0][0])
            other_var = next(v for v in KD.args if v != sum_var)
            #and finally, return test equal
            #on the collapsed sum
            return test_equal(Mul(*[x.subs(sum_var, other_var) for x in args if x != KD]),
                v2)
        #sum of vals to Ns -> sum vals to Ns - 1 + val_ns
        if isinstance(v1, Sum) and v2.has(Sum) and isinstance(v2, Add):
            lim = v1.limits[0]
            #get the Ns term, and test equivalence
            v2Ns = next((x for x in v2.args if
                test_equal(v1.function.subs(lim[0], lim[2]), x)),
                None)
            assert v2Ns is not None

            #get the sum term in v2
            v2sum = next((arg for arg in v2.args if arg != v2Ns), None)
            assert v2sum is not None
            assert v2sum.function == v1.function
            assert v2sum.limits[0][0] == lim[0]
            assert v2sum.limits[0][1] == lim[1]
            assert v2sum.limits[0][2] + 1 == lim[2]
            return True

        if v1 in equivalences:
            return any(v1t == v2 for v1t in equivalences[v1])
        elif -v1 in equivalences:
            return any(v1t == -v2 for v1t in equivalences[-v1])
        if v2 in equivalences:
            return any(v2t == v1 for v2t in equivalences[v2])
        elif -v2 in equivalences:
            return any(v2t == -v1 for v2t in equivalences[-v2])

        if simplify(v1 - v2) == 0:
            return True

        for equiv in v1.free_symbols:
            if equiv in equivalences:
                for eq in equivalences[equiv]:
                    v1test = v1.subs(equiv, eq)
                    if test_equal(v1test, v2):
                        return True

        return False

    for arg in subs_args:
        if 'assumptions' in kw_args and kw_args['assumptions']:
            assert test_equal(arg[0].subs(kw_args['assumptions']),
                arg[1].subs(kw_args['assumptions']))
        else:
            assert test_equal(arg[0], arg[1])

    return obj.subs(subs_args)


"""
ConP / ConV independent symbols
"""

assumptions = {'float' : True,
               'finite' : True,
               'negative' : False,
               'postive' : True,
               'real' : True}

#time
t = symbols('t', **assumptions)


#thermo vars
T = MyImplicitSymbol('T', t, **assumptions)

#mechanism size
Ns = S.Ns
Nr = S.Nr

#index variables
k = Idx('k', (1, Ns + 1))
i = Idx('i', (1, Nr + 1))
j = Idx('j')
l = Idx('l')
m = Idx('m')

Wk = IndexedBase('W')

#some constants, and state variables
Patm = S.atm_pressure
R = S.gas_constant
m_sym = S.mass

#polyfits
a = IndexedBase('a')


def thermo_derivation(Yi_sym, P, V, n, subfile=None):
    def write(*args):
        write_eq(*args, myfile=subfile)
    def write_dummy(*args):
        write_dummy_eq(*args, myfile=subfile)
    def write_sec(*args):
        write_section(*args, myfile=subfile)
    #derivation of thermo constants, e.g. enthalpy, cp, etc.

    cpfunc = R * (a[k, 0] + T * (a[k, 1] + T * (a[k, 2] + T * (a[k, 3] + a[k, 4] * T))))
    cp = MyIndexedFunc(r'{C_p}', T)
    cp_mass = MyIndexedFunc(r'{c_p}', T)

    cp_tot_sym = MyImplicitSymbol(r'\bar{c_p}', T)
    if hasattr(Yi_sym, '__getitem__'):
        Yi_sym = Yi_sym[k]

    cp_tot = Sum(Yi_sym * cp_mass[k], (k, 1, Ns))
    if subfile:
        write(Eq(Eq(Symbol(r'{C_{p,k}}^{\circ}'), cp[k]), cpfunc),
            expand(cpfunc))
        write(diff(cp[k], T), simplify(diff(cpfunc, T)))
        write(cp_mass[k], cp[k] / Wk[k])
        write(cp_tot_sym, cp_tot)

    cvfunc = simplify(cpfunc - R)
    cv = MyIndexedFunc(r'{C_v}', T)
    cv_mass = MyIndexedFunc(r'{c_v}', T)
    cv_tot_sym = MyImplicitSymbol(r'\bar{c_v}', T)
    cv_tot = Sum(Yi_sym * cv_mass[k], (k, 1, Ns))
    if subfile:
        write(Eq(Eq(Symbol(r'{C_{v,k}}^{\circ}'), cv[k]), cvfunc),
            expand(cvfunc))
        write(diff(cv[k], T), simplify(diff(cvfunc, T)))
        write(cv_mass[k], cv[k] / Wk[k])
        write(cv_tot_sym, cv_tot)

    hfunc = R * (T * (a[k, 0] + T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 3) + T * (a[k, 3] * Rational(1, 4) + a[k, 4] * T * Rational(1, 5))))) + a[k, 5])
    h = MyIndexedFunc(r'H', T)
    register_equal(h[k], hfunc)
    h_mass = MyIndexedFunc(r'h', T)

    #check that the dH/dT = cp identity holds
    if subfile: #only check once
        assert simplify(diff(hfunc, T) - cpfunc) == 0

    if subfile:
        write(Eq(Eq(Symbol(r'H_k^{\circ}'), h[k]), hfunc),
            expand(hfunc))
        write(diff(h[k], T), simplify(diff(hfunc, T)))
        write(h_mass[k], h[k] / Wk[k])

    u = MyIndexedFunc(r'U', T)
    u_mass = MyIndexedFunc(r'u', T)
    if subfile:
        write_dummy(r'H_k = U_k + \frac{P V}{n}')
        write(h[k], u[k] + P * V / n)
        ufunc = h[k] - P * V / n
        ufunc = collect(assert_subs(ufunc, (h[k], hfunc)), R)
        write(u[k], ufunc)
        assert simplify(diff(ufunc, T) - cvfunc) == 0

    #finally do the entropy and B terms
    Sfunc = R * (a[k, 0] * log(T) + T * (a[k, 1] + T * (a[k, 2] * Rational(1, 2) + T * (a[k, 3] * Rational(1, 3) + a[k, 4] * T * Rational(1, 4)))) + a[k, 6])
    s = MyIndexedFunc(r'S', T)
    if subfile:
        write(Eq(Eq(Symbol(r'S_k^{\circ}'), s[k]), Sfunc),
            expand(Sfunc))

    Bk = simplify(Sfunc / R - hfunc / (R * T))

    return cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass,\
            cv, cv_mass, cv_tot_sym, cv_tot, u, u_mass, Bk

def reaction_derivation(P, P_sym, V, Wk, W, Ck, Ctot_sym, n_sym, m_sym, Bk, subfile):
    def write(*args):
        write_eq(*args, myfile=subfile)
    def write_dummy(*args):
        write_dummy_eq(*args, myfile=subfile)
    def write_sec(*args):
        write_section(*args, myfile=subfile)

    write_sec('Definitions')
    nu_f = IndexedBase(r'\nu^{\prime}')
    nu_r = IndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[k, i] - nu_r[k, i]
    nu_sym = IndexedBase(r'\nu')
    write(nu_sym[k, i], nu)

    conp = P.is_constant()
    dPdT = None
    dPdCj = None
    if not conp:
        #let's get some Pressure definitions out of the way
        subfile.write('Pressure derivatives')
        P_real = R * T * n_sym / V
        write(P_sym, P_real)

        #get values for dP/dT
        dPdT = diff(P_real, T)
        write(diff(P, T), dPdT)

        mass = n_sym * assert_subs(W, (Ctot_sym, n_sym / V))

        write(m_sym, mass)
        dmdT = diff(mass, T)
        write(Eq(diff(m_sym, T), 0), dmdT)
        dmdT = factor_terms(dmdT)
        write(diff(m_sym, T), dmdT)

        dndT = solve(Eq(dmdT, 0), diff(n_sym, T))[0]
        register_equal(diff(n_sym, T), dndT)
        write(diff(n_sym, T), dndT)

        dPdT = assert_subs(dPdT, (diff(n_sym, T), dndT))
        write(diff(P, T), dPdT)
        assert dPdT == P_real / T
        dPdT = P / T
        write(diff(P, T), dPdT)
        register_equal(diff(P, T), dPdT)

        #get values for dP/dCj
        dPdCj = diff(P_real, Ck[j])
        write(diff(P, Ck[j]), dPdCj)

        dmdCj = diff(mass, Ck[j])
        write(Eq(diff(m_sym, Ck[j]), 0), dmdCj)
        dndCj = solve(Eq(dmdCj, 0), diff(n_sym, Ck[j]))[0]
        dndCj = simplify(assert_subs(dndCj, (
            Sum(-KroneckerDelta(j, k) * (Wk[Ns] - Wk[k]), (k, 1, Ns - 1)),
            -(Wk[Ns] - Wk[j]))))
        write(diff(n_sym, Ck[j]), dndCj)

        register_equal(diff(n_sym, Ck[j]), dndCj)
        dPdCj = assert_subs(dPdCj, (diff(n_sym, Ck[j]), dndCj))
        write(diff(P, Ck[j]), dPdCj)

        dPdCj = assert_subs(dPdCj, (Sum((1 - Wk[k] / Wk[Ns]) * KroneckerDelta(k, j), (k, 1, Ns - 1)),
            1 - Wk[j] / Wk[Ns]))
        register_equal(diff(P, Ck[j]), dPdCj)
        write(diff(P, Ck[j]), dPdCj)

    #define for later use
    Ctot = P / (R * T)
    Cns = Ctot - Sum(Ck[k], (k, 1, Ns - 1))
    write(Ck[Ns], Cns)
    register_equal(Ck[Ns], Cns)

    omega_sym = MyIndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck, T, nu, P_sym))
    write(diff(Ck[k], t), omega_sym[k])

    q_sym = MyIndexedFunc('q', args=(Ck, T))
    omega_k = Sum(nu_sym[k, i] * q_sym[i], (i, 1, Nr))
    write(omega_sym[k], omega_k)

    Rop_sym = MyIndexedFunc('R', args=(Ck, T))
    ci = MyIndexedFunc('c', args=(Ck, T))
    q = Rop_sym[i] * ci[i]

    write(q_sym[i], q)

    #arrhenius coeffs
    A = IndexedBase(r'A')
    Beta = IndexedBase(r'\beta')
    Ea = IndexedBase(r'{E_{a}}')

    write_sec('Rate of Progress')
    Ropf_sym = MyIndexedFunc(r'{R_f}', args=(Ck, T))
    Ropr_sym = MyIndexedFunc(r'{R_r}', args=(Ck, T))

    Rop = Ropf_sym[i] - Ropr_sym[i]
    write(Rop_sym[i], Ropf_sym[i] - Ropr_sym[i])
    register_equal(Rop_sym[i], Ropf_sym[i] - Ropr_sym[i])

    kf_sym = MyIndexedFunc(r'{k_f}', T)
    Ropf = kf_sym[i] * Product(Ck[k]**nu_f[k, i], (k, 1, Ns))
    write(Ropf_sym[i], Ropf)
    register_equal(Ropf_sym[i], Ropf)

    kr_sym = MyIndexedFunc(r'{k_r}', T)
    Ropr = kr_sym[i] * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write(Ropr_sym[i], Ropr)
    register_equal(Ropr_sym[i], Ropr)

    write_sec('Pressure Dependent Forms')
    #write the various ci forms
    ci_elem = 1
    write_dummy('c_{{i}} = {}'.format(ci_elem) + r'\text{\quad for elementary reactions}')

    ci_thd_sym = MyImplicitSymbol('[X]_i', args=(Ck, T, P_sym))
    write_dummy('c_{{i}} = {}'.format(latex(ci_thd_sym)) + r'\text{\quad for third-body enhanced reactions}')

    Pri_sym = MyImplicitSymbol('P_{r, i}', args=(T, Ck, P_sym))
    Fi_sym = MyImplicitSymbol('F_{i}', args=(T, Ck, P_sym))
    ci_fall = (Pri_sym / (1 + Pri_sym)) * Fi_sym
    write_dummy(latex(Eq(ci[i], ci_fall)) + r'\text{\quad for unimolecular/recombination falloff reactions}')
    register_equal(ci[i], ci_fall)

    ci_chem = (1 / (1 + Pri_sym)) * Fi_sym
    write_dummy(latex(Eq(ci[i], ci_chem)) + r'\text{\quad for chemically-activated bimolecular reactions}')
    register_equal(ci[i], ci_chem)

    write_sec('Forward Reaction Rate')
    kf = A[i] * (T**Beta[i]) * exp(-Ea[i] / (R * T))
    write(kf_sym[i], kf)
    register_equal(kf_sym[i], kf)


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
    register_equal(Kc_sym[i], Kc)

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
    register_equal(kr_sym[i], kf_sym[i] / Kc_sym[i])

    write_sec('Third Body Efficiencies')
    thd_bdy_eff = IndexedBase(r'\alpha')
    ci_thd = Sum(thd_bdy_eff[k, i] * Ck[k], (k, 1, Ns))
    write(ci_thd_sym, ci_thd)
    ci_thd = Ctot_sym - Sum((S.One - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns))
    write(ci_thd_sym, ci_thd)

    ci_thd = assert_subs(ci_thd, (Ctot_sym, Ctot))
    ci_thd = assert_subs(ci_thd, (Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns)),
        Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns - 1)) +
        (1 - thd_bdy_eff[Ns, i]) * Cns))
    write(ci_thd_sym, ci_thd)

    ci_thd = assert_subs(factor_terms(simplify(ci_thd)), (Ctot, Ctot_sym))
    write(ci_thd_sym, ci_thd)
    register_equal(ci_thd_sym, ci_thd)

    write_dummy(latex(Eq(ci_thd_sym, Ck[m])) + r'\text{\quad for a single species third body}')

    write_sec('Falloff Reactions')
    k0 = Symbol('A_0') * T**Symbol(r'\beta_0') * exp(-Symbol('E_{a, 0}') / (R * T))
    kinf = Symbol(r'A_{\infty}') * T**Symbol(r'\beta_{\infty}') * exp(-Symbol(r'E_{a, \infty}') / (R * T))
    k0_sym = MyImplicitSymbol(r'k_{0, i}', T)
    kinf_sym = MyImplicitSymbol(r'k_{\infty, i}', T)
    Pri_mix = ci_thd_sym  * k0_sym / kinf_sym
    write_dummy(latex(Eq(Pri_sym, Pri_mix)) + r'\text{\quad for the mixture as the third body}')
    register_equal(Pri_sym, Pri_mix)
    Pri_spec = Ck[m] * k0_sym / kinf_sym
    write_dummy(latex(Eq(Pri_sym, Pri_spec)) + r'\text{\quad for species $m$ as the third body}')
    register_equal(Pri_sym, Pri_spec)

    Fi_lind = 1
    write_dummy(latex(Eq(Fi_sym, Fi_lind)) + r'\text{\quad for Lindemann}')

    Fcent_sym = MyImplicitSymbol('F_{cent}', T)
    Atroe_sym = MyImplicitSymbol('A_{Troe}', args=(Pri_sym, Fcent_sym))
    Btroe_sym = MyImplicitSymbol('B_{Troe}', args=(Pri_sym, Fcent_sym))
    Fcent_power = (1 + (Atroe_sym / Btroe_sym)**2)**-1
    Fi_troe = Fcent_sym**Fcent_power
    Fi_troe_sym = ImplicitSymbol('F_{i}', args=(Fcent_sym, Pri_sym))
    write_dummy(latex(Eq(Fi_sym, Fi_troe)) + r'\text{\quad for Troe}')
    register_equal(Fi_troe_sym, Fi_troe)

    X_sym = MyImplicitSymbol('X', Pri_sym)
    a_fall, b_fall, c_fall, d_fall, e_fall, \
        Tstar, Tstarstar, Tstarstarstar = symbols('a b c d e T^{*} T^{**} T^{***}')
    Fi_sri = d_fall * T ** e_fall * (
        a_fall * exp(-b_fall / T) + exp(-T / c_fall))**X_sym
    write_dummy(latex(Eq(Fi_sym, Fi_sri)) + r'\text{\quad for SRI}')
    register_equal(Fi_sym, Fi_sri)

    Fcent = (S.One - a_fall) * exp(-T / Tstarstarstar) + a_fall * exp(-T / Tstar) + \
        exp(-Tstarstar / T)
    write(Fcent_sym, Fcent)

    Atroe = log(Pri_sym, 10) - Float(0.67) * log(Fcent_sym, 10) - Float(0.4)
    write(Atroe_sym, Atroe)

    Btroe = Float(0.806) - Float(1.1762) * log(Fcent_sym, 10) - Float(0.14) * log(Pri_sym, 10)
    write(Btroe_sym, Btroe)

    X = (1 + (log(Pri_sym, 10))**2)**-1
    write(X_sym, X)
    register_equal(X_sym, X)

    write_sec('Pressure-dependent Reactions')

    #pdep
    subfile.write('For PLog reactions\n')
    A_1, A_2, beta_1, beta_2, Ea_1, Ea_2 = symbols(r'A_1 A_2 \beta_1' +
        r' \beta_2 E_{a_1} E_{a_2}')
    k1 = A_1 * T**beta_1 * exp(Ea_1 / (R * T))
    k2 = A_2 * T**beta_2 * exp(Ea_2 / (R * T))
    k1_sym = MyImplicitSymbol('k_1', T)
    k2_sym = MyImplicitSymbol('k_2', T)
    write_dummy(latex(Eq(k1_sym, k1)) + r'\text{\quad at } P_1')
    write_dummy(latex(Eq(k2_sym, k2)) + r'\text{\quad at } P_2')

    kf_pdep = log(k1_sym) + (log(k2_sym) - log(k1_sym)) * (log(P) - log(Symbol('P_1'))) / (log(Symbol('P_2')) - log(Symbol('P_1')))
    kf_pdep_sym = Function('k_f')(T, P_sym)
    write(log(kf_pdep_sym), kf_pdep)
    register_equal(log(kf_pdep_sym), kf_pdep)

    #cheb
    subfile.write('For Chebyshev reactions\n')
    Tmin, Tmax, Pmin, Pmax = symbols('T_{min} T_{max} P_{min} P_{max}')
    Tred = (2 * T**-1 - Tmin**-1 - Tmax**-1) / (Tmax**-1 - Tmin**-1)
    Pred = simplify((2 * log(P, 10) - log(Pmin, 10) - log(Pmax, 10)) / (log(Pmax, 10) - log(Pmin, 10)))
    Tred_sym = MyImplicitSymbol(r'\tilde{T}', T)
    register_equal(diff(Tred_sym, T), diff(Tred, T))
    Pred_sym = MyImplicitSymbol(r'\tilde{P}', P)
    if not conp:
        register_equal(diff(Pred_sym, T), diff(Pred, T))

    Nt, Np = symbols('N_T N_P')
    eta = IndexedBase(r'\eta')
    kf_cheb = Sum(eta[i, j] * chebyshevt(m - 1, Tred_sym) * chebyshevt(j - 1, Pred_sym),
        (j, 1, Np), (m, 1, Nt))
    kf_cheb_sym = Function('k_f')(T, P_sym)
    write(log(kf_cheb_sym, 10), kf_cheb)
    write(Tred_sym, Tred)
    write(Pred_sym, Pred)

    write_sec('Derivatives')
    write(diff(omega_sym[k], T), diff(omega_k, T))
    write(diff(q_sym[i], T), diff(q, T))

    write(diff(omega_sym[k], Ck[k]), diff(omega_k, Ck[j]))
    write(diff(q_sym[i], Ck[k]), diff(q, Ck[j]))

    write_sec('Rate of Progress Derivatives')
    write(diff(Ropf_sym, T), diff(Ropf, T))
    write(diff(Ropf_sym, Ck[k]), diff(Ropf, Ck[j]))

    dCkdCj = diff(Ck[k], Ck[j])
    write_dummy(r'\frac{\partial [C_k]}{\partial [C_j]} =' + latex(
        dCkdCj))

    dCnsdCj_orig = diff(Cns, Ck[j])
    dCnsdCj = assert_subs(dCnsdCj_orig, (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), S.One))
    if not conp:
        dCnsdCj = simplify(assert_subs(dCnsdCj, (diff(P, Ck[j]), dPdCj)))

    write_dummy(r'\frac{\partial [C_{Ns}]}{\partial [C_j]} =' + latex(
        Eq(dCnsdCj_orig, dCnsdCj)))

    dCnsdCj_pow = diff(Cns**nu_f[Ns, i], Ck[j])
    write_dummy(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj_pow))

    dCnsdCj_pow = simplify(assert_subs(dCnsdCj_pow, (Cns, Ck[Ns]),
        (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1)))
    write_dummy(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj_pow))
    if not conp:

        dCnsdCj_pow = simplify(assert_subs(dCnsdCj_pow, (diff(P, Ck[j]), dPdCj)))
        write_dummy(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{k, i}}}{\partial [C_j]} =' + latex(
            dCnsdCj_pow))

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
        return krate * Sum((dCkdCj + dCnsdCj * KroneckerDelta(k, Ns)) *\
                nuv[k, i] * Ck[k] ** (nuv[k, i] - 1) * __mod_prod_sum(k, fwd), (k, 1, Ns))

    dRopfdCj = __create_dRopdCj()
    write(diff(Ropf_sym[i], Ck[j]), dRopfdCj)
    register_equal(diff(Ropf_sym[i], Ck[j]), dRopfdCj)

    dRoprdCj = __create_dRopdCj(False)
    write(diff(Ropr_sym[i], Ck[j]), dRoprdCj)
    register_equal(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    dkfdT = assert_subs(factor_terms(diff(kf, T)), (kf, kf_sym[i]))
    write(diff(kf_sym[i], T), dkfdT)
    register_equal(diff(kf_sym[i], T), dkfdT)

    dRopfdT = assert_subs(diff(Ropf, T), (diff(kf_sym[i], T), dkfdT),
        (Ropf, Ropf_sym[i]))
    write(diff(Ropf_sym[i], T), dRopfdT)
    register_equal(diff(Ropf_sym[i], T), dRopfdT)

    subfile.write('For reactions with explicit reverse Arrhenius coefficients\n')

    A_rexp = IndexedBase(r'{A_{r}}')
    Beta_rexp = IndexedBase(r'{\beta_r}')
    Ea_rexp = IndexedBase(r'{E_{a,r}}')
    kr_rexp = A_rexp[i] * T**Beta_rexp[i] * exp(-Ea_rexp[i] / (R * T))
    Ropr_rexp = kr_rexp * Product(Ck[l]**nu_r[k, i], (k, 1, Ns))
    register_equal(Ropr_rexp, Ropr_sym[i])
    dRopr_rexpdT =  diff(Ropr_rexp, T)
    dRopr_rexpdT = assert_subs(factor_terms(dRopr_rexpdT), (Ropr_rexp, Ropr_sym[i]))
    dRop_expdT = dRopfdT - dRopr_rexpdT
    dRop_expdT = assert_subs(dRop_expdT, (Ropf, Ropf_sym[i]))

    write(diff(Rop_sym[i], T), dRop_expdT)

    subfile.write('For non-explicit reversible reactions\n')
    dkrdT = diff(kf_sym[i] / Kc_sym[i], T)
    write(diff(kr_sym[i], T), dkrdT)
    dkrdT = assert_subs(dkrdT, (diff(kf_sym[i], T), dkfdT))
    dkrdT = assert_subs(dkrdT, (kf_sym[i] / Kc_sym[i], kr_sym[i]))
    dkrdT = factor_terms(dkrdT)
    write(diff(kr_sym[i], T), dkrdT)

    #dkcdT
    dKcdT = diff(Kc, T)
    dKcdT = assert_subs(dKcdT, (Kc, Kc_sym[i]))
    write(diff(Kc_sym[i], T), dKcdT)
    register_equal(diff(Kc_sym[i], T), dKcdT)

    #sub into dkrdT
    dkrdT = assert_subs(dkrdT, (diff(Kc_sym[i], T), dKcdT))
    write(diff(kr_sym[i], T), dkrdT)
    register_equal(diff(kr_sym[i], T), dkrdT)

    #now the full dRdT
    dRoprdT = assert_subs(diff(Ropr, T), (diff(kr_sym[i], T), dkrdT))
    dRoprdT = assert_subs(dRoprdT, (Ropr, Ropr_sym[i]))
    write(diff(Ropr_sym[i], T), dRoprdT)
    register_equal(diff(Ropr_sym[i], T), dRoprdT)

    dRop_nonexpdT = assert_subs(diff(Rop, T), (diff(Ropf_sym[i], T), dRopfdT),
        (diff(Ropr_sym[i], T), dRoprdT))
    write(diff(Rop_sym[i], T), dRop_nonexpdT)

    subfile.write('For all reversible reactions\n')
    #now do dRop/dCj
    dRopdCj = assert_subs(diff(Rop, Ck[j]),
        (diff(Ropf_sym[i], Ck[j]), dRopfdCj),
        (diff(Ropr_sym[i], Ck[j]), dRoprdCj))
    write(diff(Rop_sym[i], Ck[j]), dRopdCj)

    write_sec(r'Third-Body\slash Pressure-Depencence Derivatives')
    subfile.write('For elementary reactions\n')
    write(diff(ci[i], T), diff(ci_elem, T))
    write(diff(ci[i], Ck[j]), diff(ci_elem, Ck[j]))

    subfile.write('For third body enhanced reactions\n')
    dci_thddT = assert_subs(diff(assert_subs(ci_thd, (Ctot_sym, Ctot)), T),
                                (Ctot, Ctot_sym))
    if not conp:
        dci_thddT = assert_subs(dci_thddT, (diff(P, T), dPdT),
                                            (Ctot, Ctot_sym))
        write(diff(ci_thd_sym, T), dci_thddT)
    register_equal(diff(ci_thd_sym, T), dci_thddT)

    dci_thddCj = diff(assert_subs(ci_thd, (Ctot_sym, Ctot)), Ck[j])
    dci_thddCj = assert_subs(simplify(dci_thddCj),
            (Sum((thd_bdy_eff[Ns, i] - thd_bdy_eff[k, i]) *
                KroneckerDelta(j, k), (k, 1, Ns - 1)),
            thd_bdy_eff[Ns, i] - thd_bdy_eff[j, i]))
    write(diff(ci_thd_sym, Ck[j]), dci_thddCj)
    if not conp:
        dci_thddCj = assert_subs(simplify(dci_thddCj), (diff(P, Ck[j]), dPdCj))
        write(diff(ci_thd_sym, Ck[j]), dci_thddCj)
    register_equal(diff(ci_thd_sym, Ck[j]), dci_thddCj)

    subfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    dci_unity_dCj = diff(Ctot, Ck[j])
    write(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)
    if not conp:
        dci_unity_dCj = assert_subs(dci_unity_dCj, (diff(P, Ck[j]), dPdCj))
        write(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)
    register_equal(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)

    subfile.write('For unimolecular/recombination fall-off reactions\n')
    dci_falldT = factor_terms(
        collect(
            assert_subs(diff(ci_fall, T),
            (ci_fall, ci[i])),
        diff(Pri_sym, T)))
    write(diff(ci[i], T), dci_falldT)


    dci_falldCj = factor_terms(
        collect(
            assert_subs(diff(ci_fall, Ck[j]),
                (ci_fall, ci[i]))
            , diff(Pri_sym, Ck[j]) / (Pri_sym + 1)))
    write(diff(ci[i], Ck[j]), dci_falldCj)

    subfile.write('For chemically-activated bimolecular reactions\n')
    dci_chemdT = factor_terms(
        collect(
            assert_subs(diff(ci_chem, T), (ci_chem, ci[i])),
            diff(Pri_sym, T)))
    write(diff(ci[i], T), dci_chemdT)

    dci_chemdCj = factor_terms(
        collect(
            assert_subs(diff(ci_chem, Ck[j]), (ci_chem, ci[i])),
            diff(Pri_sym, Ck[j]) / (Pri_sym + 1)))
    write(diff(ci[i], Ck[j]), dci_chemdCj)

    subfile.write('The $P_{r, i}$ derivatives are:\n')
    dPri_mixdT = assert_subs(diff(Pri_mix, T), (diff(ci_thd_sym, T), dci_thddT))
    A_inf, Beta_inf = symbols(r'A_{\infty} \beta_{\infty}')
    Ea_inf = Symbol(r'E_{a, \infty}')
    register_equal([(A[i], A_inf), (Beta[i], Beta_inf), (Ea[i], Ea_inf), (kf_sym[i], kinf_sym)])

    A_0, Beta_0 = symbols(r'A_{0} \beta_{0}')
    Ea_0 = Symbol('E_{a, 0}')
    register_equal([(A[i], A_0), (Beta[i], Beta_0), (Ea[i], Ea_0), (kf_sym[i], k0_sym)])

    dkinfdT = assert_subs(dkfdT, (A[i], A_inf),
        (Beta[i], Beta_inf), (Ea[i], Ea_inf),
        (kf_sym[i], kinf_sym))
    register_equal(diff(kinf_sym, T), dkinfdT)
    dk0dT = assert_subs(dkfdT, (A[i], Symbol(r'A_{0}')),
        (Beta[i], Symbol(r'\beta_{0}')), (Ea[i], Symbol(r'E_{a, 0}')),
        (kf_sym[i], k0_sym))
    register_equal(diff(k0_sym, T), dk0dT)

    dPri_mixdT = assert_subs(dPri_mixdT, (diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT))
    dPri_mixdT = assert_subs(collect(dPri_mixdT, Pri_mix / T), (Pri_mix, Pri_sym))

    subfile.write('\nFor the mixture as the third body\n')
    write(diff(Pri_sym, T), dPri_mixdT)

    dPri_mixdCj = assert_subs(diff(Pri_mix, Ck[j]), (diff(ci_thd_sym, Ck[j]), dci_thddCj))
    dPri_mixdCj = assert_subs(dPri_mixdCj, (Sum((-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i])
            * KroneckerDelta(j, k), (k, 1, Ns - 1)),
        -thd_bdy_eff[Ns, i] + thd_bdy_eff[j, i]))
    write(diff(Pri_sym, Ck[j]), dPri_mixdCj)


    subfile.write('For species $m$ as the third body\n')

    dPri_specdT = diff(Pri_spec, T)
    dPri_specdT = assert_subs(dPri_specdT, (diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT))
    dPri_specdT = assert_subs(collect(dPri_specdT, Pri_spec / T), (Pri_spec, Pri_sym))
    write(diff(Pri_sym, T), dPri_specdT)

    dCmdCj = (1 - KroneckerDelta(m, Ns)) * diff(Ck[m], Ck[j]) + KroneckerDelta(m, Ns) * dCnsdCj
    register_equal(diff(Ck[m], Ck[j]), dCmdCj)
    dPri_specdCj = assert_subs(diff(Pri_spec, Ck[j]), (diff(Ck[m], Ck[j]), dCmdCj))
    write(diff(Pri_sym, Ck[j]), dPri_specdCj)

    subfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    Pri_unity = assert_subs(Pri_mix, (ci_thd_sym, ci_thd))
    Pri_unity = assert_subs(Pri_unity, (ci_thd, Ctot),
            assumptions=[(thd_bdy_eff[k, i], 1), (thd_bdy_eff[Ns, i], 1)])
    Pri_unity_sym = assert_subs(Pri_unity, (Ctot, Ctot_sym))
    register_equal(Pri_unity_sym, Pri_unity)
    dPri_unitydT = assert_subs(diff(Pri_unity, T), (Ctot, Ctot_sym))
    dPri_unitydT = assert_subs(dPri_unitydT, (diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT))

    dPri_unitydT = assert_subs(collect(dPri_unitydT, Pri_unity_sym / T),
                        (Pri_unity_sym, Pri_sym),
                        assumptions=[(Pri_unity_sym, Pri_sym)])
    write(diff(Pri_sym, T), dPri_unitydT)

    if not conp:
        dPri_unitydT = assert_subs(dPri_unitydT, (diff(P, T), dPdT),
            (Pri_unity, Pri_sym),
            assumptions=[(Pri_unity, Pri_sym)])
        dPri_unitydT = collect(dPri_unitydT, Pri_sym / T)
        write(diff(Pri_sym, T), dPri_unitydT)

    dPri_unitydCj = diff(Pri_unity, Ck[j])
    write(diff(Pri_sym, Ck[j]), dPri_unitydCj)

    if not conp:
        dPri_unitydCj = assert_subs(dPri_unitydCj, (diff(P, Ck[j]), dPdCj))
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
    dFi_troedFcent = assert_subs(factor_terms(
        diff(Fi_troe, Fcent_sym)), (Fi_troe, Fi_troe_sym))
    write(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)

    dFcentdT = diff(Fcent, T)
    write(diff(Fcent_sym, T), dFcentdT)
    register_equal(diff(Fcent_sym, T), dFcentdT)

    dFi_troedPri = factor_terms(
        assert_subs(diff(Fi_troe, Pri_sym),
            (Fi_troe, Fi_troe_sym)))
    write(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    subfile.write('And\n')
    dAtroedFcent = diff(Atroe, Fcent_sym)
    dBtroedFcent = diff(Btroe, Fcent_sym)
    dAtroedPri = diff(Atroe, Pri_sym)
    dBtroedPri = diff(Btroe, Pri_sym)
    write(diff(Atroe_sym, Fcent_sym), dAtroedFcent)
    register_equal(diff(Atroe_sym, Fcent_sym), dAtroedFcent)

    write(diff(Btroe_sym, Fcent_sym), dBtroedFcent)
    register_equal(diff(Btroe_sym, Fcent_sym), dBtroedFcent)

    write(diff(Atroe_sym, Pri_sym), dAtroedPri)
    register_equal(diff(Atroe_sym, Pri_sym), dAtroedPri)

    write(diff(Btroe_sym, Pri_sym), dBtroedPri)
    register_equal(diff(Btroe_sym, Pri_sym), dBtroedPri)

    subfile.write('Thus\n')
    dFi_troedFcent = factor_terms(
            assert_subs(dFi_troedFcent,
            (diff(Atroe_sym, Fcent_sym), dAtroedFcent),
            (diff(Btroe_sym, Fcent_sym), dBtroedFcent)
            ))
    write(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)
    register_equal(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)

    dFi_troedPri = factor_terms(
        assert_subs(dFi_troedPri,
            (diff(Atroe_sym, Pri_sym), dAtroedPri),
            (diff(Btroe_sym, Pri_sym), dBtroedPri))
        )
    write(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)
    register_equal(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    subfile.write('And\n')


    subfile.write('For SRI reactions\n')
    dFi_sridT = factor_terms(
        assert_subs(diff(Fi_sri, T), (Fi_sri, Fi_sym)))
    dFi_sridCj = assert_subs(diff(Fi_sri, Ck[j]),
        (Fi_sri, Fi_sym))
    write(diff(Fi_sym, T), dFi_sridT)
    write(diff(Fi_sym, Ck[j]), dFi_sridCj)

    subfile.write('Where\n')
    dXdPri = assert_subs(diff(X, Pri_sym), (X, X_sym))
    write(diff(X_sym, Pri_sym), dXdPri)
    write_dummy(r'\frac{\partial X}{\partial [C]_j} = ' + latex(diff(X_sym, Ck[j])))

    subfile.write('Thus\n')


    write_sec('Pressure-dependent reaction derivatives')
    subfile.write('For PLog reactions\n')
    dkf_pdepdT = diff(kf_pdep, T)
    #since the kf_pdep is expressed as a log
    #we need to solve for this in terms of dkf/dT
    mul_term = kf_sym[i]
    assert diff(log(kf_sym[i]), T) * mul_term == diff(kf_sym[i], T)
    dkf_pdepdT = dkf_pdepdT * mul_term
    write(diff(kf_sym[i], T), dkf_pdepdT)
    #next sub in the corresponding kf derivatives
    dk1dT = assert_subs(dkfdT, (kf_sym[i], k1_sym),
        (Beta[i], beta_1), (Ea[i], Ea_1),
        assumptions=[(kf_sym[i], k1_sym), (A[i], A_1), (Ea[i], Ea_1), (Beta[i], beta_1)])
    register_equal(diff(k1_sym, T), dk1dT)
    dk2dT = assert_subs(dkfdT, (kf_sym[i], k2_sym),
        (Beta[i], beta_2), (Ea[i], Ea_2),
        assumptions=[(kf_sym[i], k2_sym), (A[i], A_2), (Ea[i], Ea_2), (Beta[i], beta_2)])
    register_equal(diff(k2_sym, T), dk2dT)
    dkf_pdepdT = assert_subs(dkf_pdepdT, (diff(k1_sym, T), dk1dT),
        (diff(k2_sym, T), dk2dT))
    if not conp:
        dkf_pdepdT = assert_subs(dkf_pdepdT, (diff(P, T), dPdT))
    write(diff(kf_sym[i], T), dkf_pdepdT)

    #and even futher
    dkf_pdepdT = factor_terms(dkf_pdepdT)
    write(diff(kf_sym[i], T), dkf_pdepdT)

    subfile.write('For Chebyshev reactions\n')
    dkf_chebdT = diff(kf_cheb, T) * mul_term
    write(diff(kf_sym[i], T), dkf_chebdT)
    dkf_chebdT = assert_subs(dkf_chebdT, (diff(Tred_sym, T), diff(Tred, T)))
    write(diff(kf_sym[i], T), dkf_chebdT)

    if not conp:
        dkf_chebdT = assert_subs(dkf_chebdT,
                        (diff(Pred_sym, T), diff(Pred, T)),
                        (diff(P, T), dPdT))
        dkf_chebdT = factor_terms(dkf_chebdT)
        write(diff(kf_sym[i], T), dkf_chebdT)

    write_sec('Jacobian Update Form')
    subfile.write('For explicit reversible reactions')
    dqdT_exp = assert_subs(diff(q, T), (diff(Rop_sym[i], T), dRop_expdT),
        (Rop_sym[i], Ropf_sym[i] - Ropr_sym[i]),
        assumptions=[(diff(Rop_sym[i], T), dRop_expdT)])
    dqdT_exp = simplify(dqdT_exp)
    write(diff(q_sym[i], T), dqdT_exp)
    subfile.write('For non-explicit reversible reactions')
    dqdT_nonexp = assert_subs(diff(q, T), (diff(Rop_sym[i], T), dRop_nonexpdT),
        (Rop_sym[i], Ropf_sym[i] - Ropr_sym[i]),
        assumptions=[(diff(Rop_sym[i], T), dRop_nonexpdT)])
    dqdT_exp = simplify(dqdT_nonexp)
    write(diff(q_sym[i], T), dqdT_nonexp)

    return omega_sym, dPdT, dPdCj



def derivation(file, conp=True, thermo_deriv=False):
    write_section('State Variables and Definitions')
    #thermo vars
    Ck = IndexedConc('[C]', t)

    #define concentration
    if conp:
        P = S.pressure
        P_sym = S.pressure
        V = MyImplicitSymbol('V', t, **assumptions)
    else:
        P = MyImplicitSymbol('P', args=(Ck, T))
        P_sym = S.pressure
        V = S.volume
    state_vec = [T, Ck[1], Ck[2], Ck[Ns - 1]]

    #define state vector
    state_vec_str = ' = ' + r'\left\{{{}\ldots {}\right\}}'
    state = MyImplicitSymbol(r'\Phi', t)
    write_dummy_eq(str(state) + state_vec_str.format(
        ','.join([str(x) for x in state_vec[:-1]]),
        str(state_vec[-1])))

    write_dummy_eq(str(diff(state, t)) + state_vec_str.format(
        ','.join([str(diff(x, t)) for x in state_vec[:-1]]),
        str(diff(state_vec[-1], t))))

    n_sym = MyImplicitSymbol('n', args=(Ck, T), **assumptions)
    n = P * V / (R * T)
    write_eq(n_sym, n)

    Ctot_sym = MyImplicitSymbol('[C]', args=(T, P), **assumptions)
    Ctot = P / (R * T)
    write_eq(Ctot_sym, Ctot)
    register_equal([(Ctot_sym, Ctot), (Ctot_sym, n_sym / V),
        (Ctot_sym, Sum(Ck[k], (k, 1, Ns)))])
    Cns = Ctot - Sum(Ck[k], (k, 1 , Ns - 1))
    write_eq(Ck[Ns], Cns)
    register_equal(Ck[Ns], Cns)
    register_equal(Ck[Ns], assert_subs(Cns, (Ctot, Ctot_sym)))

    #mole fractions
    Xk = IndexedBase('X')
    register_equal([(Xk[k], Ck[k] / Ctot_sym)])

    #molecular weight
    W_sym = MyImplicitSymbol('W', t)
    W = Sum(Wk[k] * Xk[k], (k, 1, Ns))
    write_eq(W_sym, W)
    W = simplify(assert_subs(W, (Xk[k], Ck[k] / Ctot_sym)))
    write_eq(W_sym, W)
    Cns_sym = assert_subs(Cns, (Ctot, Ctot_sym))
    W = assert_subs(W, (Sum(Wk[k] * Ck[k], (k, 1, Ns)),
        Sum(Wk[k] * Ck[k], (k, 1, Ns - 1)) + Wk[Ns] * Cns_sym))
    write_eq(W_sym, W)
    W = simplify(W)
    write_eq(W_sym, W)

    #mass, density
    m = n * W
    density = m / V
    m_sym = MyImplicitSymbol('m', args=(T, Ck))
    density_sym = MyImplicitSymbol(r'\rho', t)
    write_eq(density_sym, n_sym * W_sym / V)
    register_equal(density_sym, W_sym * Ctot_sym)

    #mass fractions
    Yi_sym = IndexedBase('Y')
    Yi = Ck[k] * Wk[k]/ density_sym

    write_eq(Yi_sym[k], Yi)
    register_equal(Yi_sym[k], Yi)

    #get all our thermo symbols
    if thermo_deriv:
        with filer('thermo_derivation.tex', 'w') as subfile:
            therm_vals = thermo_derivation(Yi_sym, P, V, n, subfile)
    else:
        therm_vals = thermo_derivation(Yi_sym, P, V, n, None)
    cp, cp_mass, cp_tot_sym, cp_tot, h, h_mass,\
            cv, cv_mass, cv_tot_sym, cv_tot, u, u_mass, Bk = therm_vals

    #reaction rates
    with filer('con{}_reaction_derivation.tex'.format(
        'p' if conp else 'v'), 'w') as subfile:
        omega_sym, dPdT, dPdCj = reaction_derivation(P, P_sym, V, Wk, W, Ck, Ctot_sym,
             n_sym, m_sym, Bk, subfile)

    write_section('Jacobian entries')
    write_section('Energy Equation')

    if conp:
        spec_heat = cp
        spec_heat_tot = cp_tot
        spec_heat_mass = cp_mass
        total_spec_heat = cp_tot_sym
        energy_mass = h_mass
        energy = h
    else:
        spec_heat = cv
        spec_heat_tot = cv_tot
        spec_heat_mass = cv_mass
        total_spec_heat = cv_tot_sym
        energy_mass = u_mass
        energy = u

    register_equal(Wk[k] * spec_heat_mass[k], spec_heat[k])
    register_equal(Wk[k] * energy_mass[k], energy[k])
    register_equal(diff(energy[k], T), spec_heat[k])

    #temperature derivative
    #in terms of mass fraction

    dTdt_sym = diff(T, t)
    dTdt = -1 / (density_sym * total_spec_heat) * Sum(energy_mass[k] * Wk[k] * omega_sym[k], (k, 1, Ns))
    write_eq(dTdt_sym, dTdt)

    #next we turn into concentrations
    dTdt = assert_subs(dTdt, (density_sym, W_sym * Ctot_sym))
    write_eq(dTdt_sym, dTdt)

    #do some simplifcation of the cp term
    spec_heat_tot = assert_subs(spec_heat_tot, (Yi_sym[k], Yi))
    write_eq(total_spec_heat, spec_heat_tot)
    spec_heat_tot = assert_subs(simplify(spec_heat_tot), (density_sym, W_sym * Ctot_sym))
    write_eq(total_spec_heat, spec_heat_tot)
    register_equal(total_spec_heat, spec_heat_tot)

    dTdt = assert_subs(dTdt, (total_spec_heat, spec_heat_tot))
    write_eq(dTdt_sym, dTdt)

    #this will be used many times
    CkCpSum = Sum(Ck[k] * spec_heat[k], (k, 1, Ns))

    #next we swap out the mass cp's
    dTdt = assert_subs(dTdt, (Wk[k] * spec_heat_mass[k],
        spec_heat[k]), (Wk[k] * energy_mass[k], energy[k]))

    #save a copy of this form as it's very compact
    dTdt_simple = dTdt
    write_eq(dTdt_sym, dTdt)
    register_equal(dTdt_sym, dTdt_simple)

    #and simplify the full sum more
    dTdt = assert_subs(dTdt, (CkCpSum, Sum(Ck[k] * spec_heat[k], (k, 1, Ns - 1)) + Cns * spec_heat[Ns]))
    write_eq(dTdt_sym, dTdt)

    num, den = fraction(dTdt)
    den = assert_subs(simplify(den), (Ctot, Ctot_sym))

    dTdt = num / den
    CkCpSum_full = den
    register_equal(CkCpSum_full, CkCpSum)
    write_eq(dTdt_sym, dTdt)

    #Temperature jacobian entries

    write_section(r'$\dot{T}$ Derivatives')
    file.write('Concentration derivative\n')
    #first we do the concentration derivative
    dTdotdC_sym = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    dTdotdC = simplify(diff(dTdt, Ck[j]))
    write_eq(dTdotdC_sym, dTdotdC)

    if not conp:
        dTdotdC = assert_subs(dTdotdC, (diff(Ctot_sym, P), diff(Ctot, P)),
            (diff(P, Ck[j]), dPdCj))
        write_eq(dTdotdC_sym, dTdotdC)

    #Compact the CkCpSum back to a more reasonble representation
    #for sanity
    def __powsimp(expr):
        assert len(expr.args) == 2
        expr, power = expr.args
        return simplify(expr)**power

    dTdotdC_rep = 0
    for term in Add.make_args(dTdotdC):
        num, den = fraction(term)
        num = factor_terms(
            assert_subs(simplify(num), (CkCpSum_full, CkCpSum)))
        if isinstance(den, Pow):
            den = assert_subs(__powsimp(den),
                (CkCpSum_full, CkCpSum))
        else:
            den = assert_subs(simplify(den),
                (CkCpSum_full, CkCpSum))
        dTdotdC_rep = dTdotdC_rep + num / den
    dTdotdC = dTdotdC_rep
    write_eq(dTdotdC_sym, dTdotdC)

    #another level of compactness, replaces the kronecker delta sum
    dTdotdC = assert_subs(dTdotdC, (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1),
        (Sum(KroneckerDelta(j, k) * spec_heat[k], (k, 1, Ns - 1)), spec_heat[j]))
    write_eq(dTdotdC_sym, dTdotdC)

    #now expand to replace with the dT/dt term
    def __factor_denom(expr):
        num, den = fraction(ratsimp(expr))
        arg, power = den.args
        return Add(*[simplify(x) / arg for x in Add.make_args(num)]) / arg**(power - 1)

    dTdotdC = __factor_denom(dTdotdC)
    write_eq(dTdotdC_sym, dTdotdC)

    dTdotdC = collect(dTdotdC, dTdt_simple)
    dTdotdC = assert_subs(dTdotdC, (-dTdt_simple, -dTdt_sym),
        (dTdt_simple, dTdt_sym))
    write_eq(dTdotdC_sym, dTdotdC)

    file.write('Temperature derivative\n')

    write_eq(dTdt_sym, dTdt)
    #up next the temperature derivative
    dTdotdT_sym = symbols(r'\frac{\partial\dot{T}}{\partial{T}}')
    #first we must sub in the actual form of C, as the temperature derivative is non-zero
    starting = assert_subs(dTdt, (Ctot_sym, Ctot))
    write_eq(dTdt_sym, starting)
    dTdotdT = diff(starting, T)

    write_eq(dTdotdT_sym, dTdotdT)

    #sub in dPdT
    if not conp:
        dTdotdT = assert_subs(dTdotdT, (diff(P, T), dPdT))

    #first up, go back to Ctot_sym
    dTdotdT = dTdotdT.subs(Ctot, Ctot_sym)
    write_eq(dTdotdT_sym, dTdotdT)

    #and collapse the cp sum
    rv = 0
    for arg in Add.make_args(dTdotdT):
        num, den = fraction(arg)
        if isinstance(den, Pow):
            rv = rv + num / assert_subs(__powsimp(den), (CkCpSum_full, CkCpSum))
        else:
            rv = rv + num / assert_subs(simplify(den), (CkCpSum_full, CkCpSum))
    dTdotdT = rv
    write_eq(dTdotdT_sym, dTdotdT)

    #now we factor out the Ck cp sum
    dTdotdT = factor_terms(dTdotdT)
    write_eq(dTdotdT_sym, dTdotdT)

    #and replace the dTdt term
    dTdotdT = assert_subs(dTdotdT, (dTdt_simple, dTdt_sym),
        (-dTdt_simple, -dTdt_sym))
    write_eq(dTdotdT_sym, dTdotdT)

    #the next simplification is of the [C] terms
    num, den = fraction(dTdotdT)
    num = assert_subs(num, (Ctot_sym, Sum(Ck[k], (k, 1, Ns))))
    dTdotdT = num / den
    write_eq(dTdotdT_sym, dTdotdT)

    num = assert_subs(num, (Sum(Ck[k], (k, 1, Ns)), Sum(Ck[k], (k, Ns, Ns)) + Sum(Ck[k], (k, 1, Ns - 1))))
    num = collect(simplify(num), dTdt_sym)
    if conp:
        num = assert_subs(num, ((-diff(spec_heat[Ns], T) + spec_heat[Ns] / T) * Sum(Ck[k], (k, Ns, Ns)),
            Sum((-diff(spec_heat[k], T) + spec_heat[Ns] / T) * Ck[k], (k, Ns, Ns))))
    else:
        num = assert_subs(num, (-diff(spec_heat[Ns], T) * Sum(Ck[k], (k, Ns, Ns)),
            Sum(-diff(spec_heat[k], T) * Ck[k], (k, Ns, Ns))))
    num = collect(simplify(num), dTdt_sym)

    dTdotdT = num / den
    write_eq(dTdotdT_sym, dTdotdT)

    #and finally substitute the energy derivative
    dTdotdT = assert_subs(dTdotdT, (diff(energy[k], T), spec_heat[k]))
    write_eq(dTdotdT_sym, dTdotdT)

    write_section(r'$\dot{C_k}$ Derivatives')

    #concentration Jacobian equations
    dCdot = MyIndexedFunc(r'\dot{C}', (Ck, T))
    write_eq(diff(dCdot[k], Ck[j]), diff(omega_sym[k], Ck[j]))
    write_eq(diff(dCdot[k], T), diff(omega_sym[k], T))


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

    from argparse import ArgumentParser
    parser = ArgumentParser(description='generates derivations for SPyJac')
    parser.add_argument('-conv', '--constant_volume',
                         action='store_true',
                         default=False)

    args = parser.parse_args()
    conv = args.constant_volume

    with filer('con{}_derivation.tex'.format('v' if conv else 'p'), 'w') as file:
        derivation(file, not conv, True)