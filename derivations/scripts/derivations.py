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
from sympy.core.function import UndefinedFunction, Function, diff, Derivative, expand, expand_mul, count_ops
from sympy.functions.elementary.exponential import exp, log, sqrt
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.functions.special.polynomials import chebyshevt, chebyshevu
from sympy.core.numbers import Rational, Float, Integer
from sympy.core.exprtools import factor_terms
from sympy.core.relational import Equality
from sympy.core.singleton import S
from sympy.printing.repr import srepr


from constants import *
from sympy_addons import *
from reaction_types import *
import os

home_dir = os.path.dirname(os.path.realpath(__file__))
out_dir = os.path.realpath(os.path.join(
    home_dir, '..', 'tex'))

init_printing()

#weights taken from http://arxiv.org/pdf/1506.03997.pdf
#note these are rough estimates and hardware dependent
#feel free to change
def count_ops_div(expr, div_weight=34, mul_weight=5, add_weight=3,
    large_factor=100):
    expr = count_ops(expr, visual=True)
    expr = expr.xreplace({Symbol('DIV') : div_weight,
                          Symbol('MUL') : mul_weight,
                          Symbol('ADD') : add_weight,
                          Symbol('NEG') : mul_weight,
                          Symbol('SUB') : add_weight}
                          )
    #everything else is powers, exp, log, etc, so replace with large factor
    expr = expr.xreplace({x : large_factor for x in expr.free_symbols})
    return expr

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
    if len(args) == 2:
        file.write(latex(Eq(args[0], args[1]), mode='equation') + '\n')
    else:
        file.write(latex(*args, mode='equation') + '\n')
    if 'sympy' in kw_args and kw_args['sympy']:
        assert len(args) == 2
        efile.write(args[0], args[1])
    if 'register' in kw_args and kw_args['register']:
        if len(args) != 2:
            assert "I don't know how to register this!"
        register_equal(args[0], args[1])

def write_dummy_eq(text, **kw_args):
    file.write(r'\begin{equation}' + text + r'\end{equation}' + '\n')

def write_conditional(arg1, arg2, text=None, enum_conds=None, register=False):
    if text is not None:
        outtext = r'\begin{equation}' + latex(arg1) + '=' + latex(arg2) +\
            r'\text{{{}}}'.format(text) + r'\end{equation}'
    else:
        outtext = latex(Eq(arg1, arg2), mode='equation')
    file.write(outtext + '\n')
    if enum_conds is not None:
        efile.write_conditional(arg1, (arg2, enum_conds))
    if register:
        assert enum_conds is None
        register_equal(arg1, arg2)

def write_section(title, **kw_args):
    sec_type = ''
    if 'sub' in kw_args and kw_args['sub']:
        sec_type = 'sub'
    elif 'subsub' in kw_args and kw_args['subsub']:
        sec_type = 'subsub'
    file.write(r'\{0}section{{{1}}}'.format(sec_type, title) + '\n')

def write_cases(variable, case_list, **kw_args):
    file.write(r'\begin{dgroup}' + '\n')

    for case_var, case_text in case_list:
        file.write(r'\begin{{dmath}} {} = {}\text{{\quad if {}}}\end{{dmath}}'.format(
            latex(variable), latex(case_var), case_text) + '\n')
    file.write(r'\end{dgroup}' + '\n')

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
                if isinstance(term, Sum) or isinstance(term, Product):
                    limit_list = ()
                    for limit in term.limits:
                        #test that we can actually compare the limits
                        try:
                            if limit[1] >= limit[2]: #and that the second >= first
                                #no sum/product
                                continue
                        except:
                            pass
                        #valid limit
                        limit_list = limit_list + (limit,)
                    if not limit_list:
                        #no remaining valid limits
                        out_terms.append(term.function.subs(term.limits[0][0], term.limits[0][1]))
                    else:
                        out_terms.append(term.__class__(term.function, *limit_list))
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
        if v1.has(KroneckerDelta) and (isinstance(v1, Sum)
            or (isinstance(v1, Mul) and v1.has(Sum))):
            if isinstance(v1, Mul) and v1.has(Sum):
                #refactor to get the Sum form
                sumv = next(x for x in Mul.make_args(v1) if isinstance(x, Sum))
                sumv = Sum(Mul(*([sumv.function] + [x for x in Mul.make_args(v1) if x != sumv])), sumv.limits)
            else:
                sumv = v1
            #get the KD term
            func = sumv.function
            args = Mul.make_args(factor_terms(func))
            KD = next((x for x in args if isinstance(x, KroneckerDelta)), None)
            #check that the substitution is formatted as we thought
            assert KD is not None
            #and that the KD includes the summation variable
            sum_var = next(v for v in KD.args if v == sumv.limits[0][0])
            other_var = next(v for v in KD.args if v != sum_var)
            #and finally, return test equal
            #on the collapsed sum
            return test_equal(Mul(*[x.subs(sum_var, other_var) for x in args if x != KD]),
                v2)
        #sum of vals to Ns -> sum vals to Ns - 1 + val_ns
        #OR
        #product of vals to Ns -> product vals to Ns - 1 * val_ns
        #OR
        #the reverse
        def __sum_test(v1, v2):
            lim = v1.limits[0]
            #get the Ns term, and test equivalence
            v2Ns = next((x for x in v2.args if
                test_equal(v1.function.subs(lim[0], lim[2]), x)),
                None)
            retv = True
            retv = retv and v2Ns is not None

            #get the sum term in v2
            v2sum = next((arg for arg in v2.args if arg != v2Ns), None)
            retv = retv and v2sum is not None
            retv = retv and v2sum.function == v1.function
            retv = retv and v2sum.limits[0][0] == lim[0]
            retv = retv and v2sum.limits[0][1] == lim[1]
            retv = retv and v2sum.limits[0][2] + 1 == lim[2]
            return retv

        if (isinstance(v1, Sum) and v2.has(Sum) and isinstance(v2, Add))\
            or (isinstance(v1, Product) and v2.has(Product) and isinstance(v2, Mul)):
            if __sum_test(v1, v2):
                return True
        if (isinstance(v2, Sum) and v1.has(Sum) and isinstance(v1, Add))\
            or (isinstance(v2, Product) and v1.has(Product) and isinstance(v1, Mul)):
            if __sum_test(v2, v1):
                return True

        #test switch of sum variable
        if (((isinstance(v1, Sum) and isinstance(v2, Sum)) or
            (isinstance(v1, Product) and isinstance(v2, Product))) and
            v2.function.subs(v2.limits[0][0], v1.limits[0][0]) == v1.function and
            v2.limits[0][1:] == v1.limits[0][1:]):
            return True

        if v1 in equivalences:
            return any(v1t == v2 for v1t in equivalences[v1])
        elif -v1 in equivalences:
            return any(v1t == -v2 for v1t in equivalences[-v1])
        if v2 in equivalences:
            return any(v2t == v1 for v2t in equivalences[v2])
        elif -v2 in equivalences:
            return any(v2t == -v1 for v2t in equivalences[-v2])

        if expand(v1 - v2) == 0:
            return True

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

def derivation(file, efile, conp=True, thermo_deriv=False):
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
    write_eq(Ctot_sym, Ctot, sympy=True)
    register_equal([(Ctot_sym, Ctot), (Ctot_sym, n_sym / V),
        (Ctot_sym, Sum(Ck[k], (k, 1, Ns)))])
    Cns = Ctot_sym - Sum(Ck[k], (k, 1 , Ns - 1))
    write_eq(Ck[Ns], Cns, sympy=True)
    Cns = assert_subs(Cns, (Ctot_sym, Ctot))
    write_eq(Ck[Ns], Cns, register=True)
    register_equal(Ck[Ns], assert_subs(Cns, (Ctot, Ctot_sym)))

    #mole fractions
    Xk = IndexedBase('X')
    register_equal(Xk[k], Ck[k] / Ctot_sym)

    #molecular weight
    W_sym = MyImplicitSymbol('W', t)
    W = Sum(Wk[k] * Xk[k], (k, 1, Ns))
    write_eq(W_sym, W)
    W = simplify(assert_subs(W, (Xk[k], Ck[k] / Ctot_sym)))
    write_eq(W_sym, W, sympy=True)
    Cns_sym = assert_subs(Cns, (Ctot, Ctot_sym))
    W = assert_subs(W, (Sum(Wk[k] * Ck[k], (k, 1, Ns)),
        Sum(Wk[k] * Ck[k], (k, 1, Ns - 1)) + Wk[Ns] * Cns_sym))
    write_eq(W_sym, W)
    W = simplify(W)
    write_eq(W_sym, W)

    #mass, density
    mass = n * W
    density = mass / V
    m_sym = MyImplicitSymbol('m', args=(T, Ck))
    density_sym = MyImplicitSymbol(r'\rho', t)
    write_eq(density_sym, n_sym * W_sym / V)
    register_equal(density_sym, W_sym * Ctot_sym)

    #mass fractions
    Yi_sym = IndexedBase('Y')
    Yi = Ck[k] * Wk[k]/ density_sym

    write_eq(Yi_sym[k], Yi, register=True)

    write_section('Thermo Definitions')

    #thermo derivation
    cpfunc = R * (a[k, 0] + T * (a[k, 1] + T * (a[k, 2] + T * (a[k, 3] + a[k, 4] * T))))
    cp = MyIndexedFunc(r'{C_p}', T)
    cp_mass = MyIndexedFunc(r'{c_p}', T)

    cp_tot_sym = MyImplicitSymbol(r'\bar{c_p}', T)

    cp_tot = Sum(Yi_sym[k] * cp_mass[k], (k, 1, Ns))
    write_eq(Symbol(r'{C_{p,k}}^{\circ}'), cp[k])
    write_eq(cp[k], cpfunc, sympy=True)
    write_eq(cp[k], expand(cpfunc))
    write_eq(diff(cp[k], T), simplify(diff(cpfunc, T)))
    dcpdT = R * (a[k, 1] + T * (2 * a[k, 2] + T * (3 * a[k, 3]  + 4 * a[k, 4] * T)))
    dcpdT = simplify(diff(cpfunc, T), measure=count_ops_div)
    write_eq(diff(cp[k], T), dcpdT, sympy=True)
    write_eq(cp_mass[k], cp[k] / Wk[k])
    write_eq(cp_tot_sym, cp_tot)

    cvfunc = simplify(cpfunc - R)
    cv = MyIndexedFunc(r'{C_v}', T)
    cv_mass = MyIndexedFunc(r'{c_v}', T)
    cv_tot_sym = MyImplicitSymbol(r'\bar{c_v}', T)
    cv_tot = Sum(Yi_sym[k] * cv_mass[k], (k, 1, Ns))
    write_eq(Symbol(r'{C_{v,k}}^{\circ}'), cv[k])
    write_eq(cv[k], cvfunc, sympy=True)
    write_eq(cv[k], expand(cvfunc))
    write_eq(diff(cv[k], T), simplify(diff(cvfunc, T)))
    dcvdT = simplify(diff(cvfunc, T), measure=count_ops_div)
    write_eq(diff(cv[k], T), dcvdT, sympy=True)
    write_eq(cv_mass[k], cv[k] / Wk[k])
    write_eq(cv_tot_sym, cv_tot)

    hfunc = R * (T * (a[k, 0] + T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 3) + T * (a[k, 3] * Rational(1, 4) + a[k, 4] * T * Rational(1, 5))))) + a[k, 5])
    h = MyIndexedFunc(r'H', T)
    h_mass = MyIndexedFunc(r'h', T)

    #check that the dH/dT = cp identity holds
    write_eq(Symbol(r'H_k^{\circ}'), h[k])
    write_eq(h[k], hfunc, sympy=True, register=True)
    write_eq(h[k], expand(hfunc))
    dhdT = simplify(diff(hfunc, T), measure=count_ops_div)
    write_eq(diff(h[k], T), dhdT, sympy=True)
    write_eq(h_mass[k], h[k] / Wk[k])

    #and du/dT
    u = MyIndexedFunc(r'U', T)
    u_mass = MyIndexedFunc(r'u', T)
    write_dummy_eq(r'H_k = U_k + \frac{P V}{n}')
    write_eq(h[k], u[k] + P * V / n)
    ufunc = h[k] - P * V / n
    ufunc = collect(assert_subs(ufunc, (h[k], hfunc)), R)
    write_eq(u[k], ufunc, sympy=True)
    dudT = simplify(diff(ufunc, T), measure=count_ops_div)
    write_eq(diff(u[k], T), dudT, sympy=True)

    #finally do the entropy and B terms
    Sfunc = R * (a[k, 0] * log(T) + T * (a[k, 1] + T * (a[k, 2] * Rational(1, 2) + T * (a[k, 3] * Rational(1, 3) + a[k, 4] * T * Rational(1, 4)))) + a[k, 6])
    s = MyIndexedFunc(r'S', T)
    write_eq(Eq(Eq(Symbol(r'S_k^{\circ}'), s[k]), Sfunc),
        expand(Sfunc))

    Jac = IndexedBase(r'\mathcal{J}', (Ns - 1, Ns - 1))

    #reaction rates
    write_section('Definitions')
    nu_f = IndexedBase(r'\nu^{\prime}')
    nu_r = IndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[k, i] - nu_r[k, i]
    nu_sym = IndexedBase(r'\nu')
    write_eq(nu_sym[k, i], nu)

    conp = P.is_constant()
    dPdT = None
    dPdCj = None
    if not conp:
        #let's get some Pressure definitions out of the way
        file.write('Pressure derivatives')
        P_real = R * T * n_sym / V
        write_eq(P_sym, P_real, sympy=True)

        #get values for dP/dT
        dPdT = diff(P_real, T)
        write_eq(diff(P, T), dPdT)

        mass = n_sym * assert_subs(W, (Ctot_sym, n_sym / V))

        write_eq(m_sym, mass)
        dmdT = diff(mass, T)
        write_eq(Eq(diff(m_sym, T), 0), dmdT)
        dmdT = factor_terms(dmdT)
        write_eq(diff(m_sym, T), dmdT)

        dndT = solve(Eq(dmdT, 0), diff(n_sym, T))[0]
        write_eq(diff(n_sym, T), dndT, register=True)

        dPdT = assert_subs(dPdT, (diff(n_sym, T), dndT))
        write_eq(diff(P, T), dPdT)
        assert dPdT == P_real / T
        dPdT = P / T
        write_eq(diff(P, T), dPdT, register=True)

        #get values for dP/dCj
        dPdCj = diff(P_real, Ck[j])
        write_eq(diff(P, Ck[j]), dPdCj)

        dmdCj = diff(mass, Ck[j])
        write_eq(Eq(diff(m_sym, Ck[j]), 0), dmdCj)
        dndCj = solve(Eq(dmdCj, 0), diff(n_sym, Ck[j]))[0]
        dndCj = simplify(assert_subs(dndCj, (
            Sum(-KroneckerDelta(j, k) * (Wk[Ns] - Wk[k]), (k, 1, Ns - 1)),
            -(Wk[Ns] - Wk[j]))))
        write_eq(diff(n_sym, Ck[j]), dndCj, register=True)

        dPdCj = assert_subs(dPdCj, (diff(n_sym, Ck[j]), dndCj))
        write_eq(diff(P, Ck[j]), dPdCj)

        dPdCj = assert_subs(dPdCj, (Sum((1 - Wk[k] / Wk[Ns]) * KroneckerDelta(k, j), (k, 1, Ns - 1)),
            1 - Wk[j] / Wk[Ns]))
        write_eq(diff(P, Ck[j]), dPdCj, register=True)

    #define for later use
    #Ctot = P / (R * T)
    #Cns = Ctot - Sum(Ck[k], (k, 1, Ns - 1))
    #write_eq(Ck[Ns], Cns)
    register_equal(Ck[Ns], Cns)

    omega_sym = MyIndexedFunc(Symbol(r'\dot{\omega}'), args=(Ck, T, nu, P_sym))
    write_eq(diff(Ck[k], t), omega_sym[k])

    q_sym = MyIndexedFunc('q', args=(Ck, T))
    omega_k = Sum(nu_sym[k, i] * q_sym[i], (i, 1, Nr))
    write_eq(omega_sym[k], omega_k)

    Rop_sym = MyIndexedFunc('R', args=(Ck, T))
    ci = MyIndexedFunc('c', args=(Ck, T))
    q = Rop_sym[i] * ci[i]

    write_eq(q_sym[i], q, register=True)
    omega_k = assert_subs(omega_k, (q_sym[i], q))
    write_eq(omega_sym[k], omega_k, sympy=True)

    #arrhenius coeffs
    A = IndexedBase(r'A')
    Beta = IndexedBase(r'\beta')
    Ea = IndexedBase(r'{E_{a}}')

    write_section('Rate of Progress')
    Ropf_sym = MyIndexedFunc(r'{R_f}', args=(Ck, T))
    Ropr_sym = MyIndexedFunc(r'{R_r}', args=(Ck, T))

    Rop = Ropf_sym[i] - Ropr_sym[i]
    write_eq(Rop_sym[i], Ropf_sym[i] - Ropr_sym[i], sympy=True, register=True)

    kf_sym = MyIndexedFunc(r'{k_f}', T)
    Ropf = kf_sym[i] * Product(Ck[k]**nu_f[k, i], (k, 1, Ns))
    write_eq(Ropf_sym[i], Ropf, sympy=True, register=True)

    kr_sym = MyIndexedFunc(r'{k_r}', T)
    Ropr = kr_sym[i] * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write_eq(Ropr_sym[i], Ropr, sympy=True, register=True)

    write_section('Third-body effect')
    #write the various ci forms
    ci_elem = Integer(1)
    write_conditional(ci[i], ci_elem, r'\quad for elementary reactions', enum_conds=reaction_type.elementary)

    ci_thd_sym = MyImplicitSymbol('[X]_i', args=(Ck, T, P_sym))
    write_conditional(ci[i], ci_thd_sym, r'\quad for third-body enhanced reactions', enum_conds=reaction_type.thd)

    Pri_sym = MyImplicitSymbol('P_{r, i}', args=(T, Ck, P_sym))
    Fi_sym = MyImplicitSymbol('F_{i}', args=(T, Ck, P_sym))
    ci_fall = (Pri_sym / (1 + Pri_sym)) * Fi_sym
    write_conditional(ci[i], ci_fall, r'\quad for unimolecular/recombination falloff reactions', 
        enum_conds=[reaction_type.pdep, pdep_form.fall])

    ci_chem = (1 / (1 + Pri_sym)) * Fi_sym
    write_conditional(ci[i], ci_chem, r'\quad for chemically-activated bimolecular reactions',
        enum_conds=[reaction_type.pdep, pdep_form.chem])

    write_section('Forward Reaction Rate')
    kf = A[i] * (T**Beta[i]) * exp(-Ea[i] / (R * T))
    write_eq(kf_sym[i], kf, sympy=True, register=True)

    write_section('Equilibrium Constants')
    Kp_sym = MyIndexedFunc(r'{K_p}', args=(T, a))
    Kc_sym = MyIndexedFunc(r'{K_c}', args=(T))
    write_eq(Kc_sym[i], Kp_sym[i] * ((Patm / (R * T))**Sum(nu_sym[k, i], (k, 1, Ns))))

    write_dummy_eq(latex(Kp_sym[i]) + ' = ' +
        r'\text{exp}(\frac{\Delta S^{\circ}_k}{R_u} - \frac{\Delta H^{\circ}_k}{R_u T})')
    write_dummy_eq(latex(Kp_sym[i]) + ' = ' +
        r'\text{exp}(\sum_{k=1}^{N_s}\frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T})')

    B_sym = MyIndexedFunc('B', T)
    Kc = ((Patm / R)**Sum(nu_sym[k, i], (k, 1, Ns))) * exp(Sum(nu_sym[k, i] * B_sym[k], (k, 1, Ns)))
    write_eq(Kc_sym[i], Kc, sympy=True, register=True)

    write_dummy_eq(latex(B_sym[k]) + r'= \frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T} - ln(T)')

    Bk = simplify(Sfunc / R - hfunc / (R * T) - log(T))
    Bk_rep = a[k, 6] - a[k, 0] + (a[k, 0] - Integer(1))*log(T) +\
        T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 6) + T * \
            (a[k, 3] * Rational(1, 12) + a[k, 4] * T * Rational(1, 20)))) - \
        a[k, 5] / T

    Bk = assert_subs(Bk, (Bk, Bk_rep))
    write_eq(B_sym[k], Bk, register=True, sympy=True)

    write_section('Reverse Reaction Rate')
    kr = kf / Kc
    kr_sym = MyIndexedFunc(r'{k_r}', args=(T))
    write_conditional(kr_sym[i], kf_sym[i] / Kc_sym[i], r'\quad if non-explicit',
        enum_conds=reversible_type.non_explicit)
    register_equal(kr_sym[i], kf_sym[i] / Kc_sym[i])

    write_section('Third-Body Efficiencies')
    thd_bdy_eff = IndexedBase(r'\alpha')
    ci_thd = Sum(thd_bdy_eff[k, i] * Ck[k], (k, 1, Ns))
    write_eq(ci_thd_sym, ci_thd)
    ci_thd = Ctot_sym - Sum((S.One - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns))
    write_conditional(ci_thd_sym, ci_thd, enum_conds=thd_body_type.mix)

    ci_thd = assert_subs(ci_thd, (Ctot_sym, Ctot))
    ci_thd = assert_subs(ci_thd, (Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns)),
        Sum((1 - thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns - 1)) +
        (1 - thd_bdy_eff[Ns, i]) * Cns))
    write_eq(ci_thd_sym, ci_thd)

    ci_thd = assert_subs(factor_terms(simplify(ci_thd)), (Ctot, Ctot_sym))
    write_eq(ci_thd_sym, ci_thd, register=True)

    write_conditional(ci_thd_sym, Ck[m], text=r'\quad for a single species third-body', 
        enum_conds=thd_body_type.single)

    write_section('Falloff Reactions')
    k0 = Symbol('A_0') * T**Symbol(r'\beta_0') * exp(-Symbol('E_{a, 0}') / (R * T))
    kinf = Symbol(r'A_{\infty}') * T**Symbol(r'\beta_{\infty}') * exp(-Symbol(r'E_{a, \infty}') / (R * T))
    k0_sym = MyImplicitSymbol(r'k_{0, i}', T)
    write_eq(k0_sym, k0, sympy=True, register=True)
    kinf_sym = MyImplicitSymbol(r'k_{\infty, i}', T)
    write_eq(kinf_sym, kinf, sympy=True, register=True)

    Pri_mix = ci_thd_sym  * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_mix, text=r'\quad for the mixture as the third-body',
        enum_conds=[thd_body_type.mix])
    
    Pri_spec = Ck[m] * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_spec, text=r'\quad for species $m$ as the third-body',
        enum_conds=[thd_body_type.single])

    Pri_unity = Ctot_sym * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_spec, text=r'\quad for for all $\alpha_{i, j} = 1$',
        enum_conds=[thd_body_type.unity])

    Fi_lind = Integer(1)
    write_conditional(Fi_sym, Fi_lind, text=r'\quad for Lindemann', 
        enum_conds=[reaction_type.pdep, falloff_form.lind])

    Fcent_sym = MyImplicitSymbol('F_{cent}', T)
    Atroe_sym = MyImplicitSymbol('A_{Troe}', args=(Pri_sym, Fcent_sym))
    Btroe_sym = MyImplicitSymbol('B_{Troe}', args=(Pri_sym, Fcent_sym))
    Fcent_power = (1 + (Atroe_sym / Btroe_sym)**2)**-1
    Fi_troe = Fcent_sym**Fcent_power
    Fi_troe_sym = ImplicitSymbol('F_{i}', args=(Fcent_sym, Pri_sym))
    register_equal(Fi_troe_sym, Fi_troe)
    write_conditional(Fi_sym, Fi_troe, text=r'\quad for Troe',
        enum_conds=[reaction_type.pdep, falloff_form.troe])

    X_sym = MyImplicitSymbol('X', Pri_sym)
    a_fall, b_fall, c_fall, d_fall, e_fall, \
        Tstar, Tstarstar, Tstarstarstar = symbols('a b c d e T^{*} T^{**} T^{***}')
    Fi_sri = d_fall * T ** e_fall * (
        a_fall * exp(-b_fall / T) + exp(-T / c_fall))**X_sym
    write_conditional(Fi_sym, Fi_sri, text=r'\quad for SRI',
        enum_conds=[reaction_type.pdep, falloff_form.sri])

    Fcent = (S.One - a_fall) * exp(-T / Tstarstarstar) + a_fall * exp(-T / Tstar) + \
        exp(-Tstarstar / T)
    write_eq(Fcent_sym, Fcent, register_equal=True, sympy=True)

    Atroe = log(Pri_sym, 10) - Float(0.67) * log(Fcent_sym, 10) - Float(0.4)
    write_eq(Atroe_sym, Atroe, register_equal=True, sympy=True)

    Btroe = Float(0.806) - Float(1.1762) * log(Fcent_sym, 10) - Float(0.14) * log(Pri_sym, 10)
    write_eq(Btroe_sym, Btroe, register_equal=True, sympy=True)

    X = (1 + (log(Pri_sym, 10))**2)**-1
    write_eq(X_sym, X, register_equal=True, sympy=True)

    write_section('Pressure-Dependent Reactions')

    #pdep
    file.write('For PLog reactions\n')
    A_1, A_2, beta_1, beta_2, Ea_1, Ea_2 = symbols(r'A_1 A_2 \beta_1' +
        r' \beta_2 E_{a_1} E_{a_2}')
    k1 = A_1 * T**beta_1 * exp(Ea_1 / (R * T))
    k2 = A_2 * T**beta_2 * exp(Ea_2 / (R * T))
    k1_sym = MyImplicitSymbol('k_1', T)
    k2_sym = MyImplicitSymbol('k_2', T)
    write_conditional(k1_sym, k1, text=r'\quad at $P_1$')
    write_conditional(k2_sym, k2, text=r'\quad at $P_2$')

    kf_pdep = log(k1_sym) + (log(k2_sym) - log(k1_sym)) * (log(P) - log(Symbol('P_1'))) / (log(Symbol('P_2')) - log(Symbol('P_1')))
    kf_pdep_sym = Function('k_f')(T, P_sym)
    write_eq(log(kf_pdep_sym), kf_pdep, register=True, sympy=True)

    #cheb
    file.write('For Chebyshev reactions\n')
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
    kf_cheb = Sum(eta[l, j] * chebyshevt(j - 1, Tred_sym) * chebyshevt(l - 1, Pred_sym),
        (l, 1, Np), (j, 1, Nt))
    kf_cheb_sym = Function('k_f')(T, P_sym)
    write_eq(log(kf_cheb_sym, 10), kf_cheb, register_equal=True, sympy=True)
    write_eq(Tred_sym, Tred, register_equal=True, sympy=True)
    write_eq(Pred_sym, Pred, register_equal=True, sympy=True)

    write_section('Derivatives')
    write_eq(diff(omega_sym[k], T), diff(omega_k, T))
    write_eq(diff(q_sym[i], T), diff(q, T))

    write_eq(diff(omega_sym[k], Ck[k]), diff(omega_k, Ck[j]))
    write_eq(diff(q_sym[i], Ck[k]), diff(q, Ck[j]))

    write_section('Rate of Progress Derivatives')

    write_section('Concentration Derivatives', sub=True)
    write_eq(diff(Ropf_sym, Ck[k]), diff(Ropf, Ck[j]))

    dCkdCj = diff(Ck[k], Ck[j])
    write_dummy_eq(r'\frac{\partial [C_k]}{\partial [C_j]} =' + latex(
        dCkdCj))

    dCnsdCj_orig = diff(Cns, Ck[j])
    dCnsdCj = assert_subs(dCnsdCj_orig, (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), S.One))
    if not conp:
        dCnsdCj = simplify(assert_subs(dCnsdCj, (diff(P, Ck[j]), dPdCj)))

    write_dummy_eq(r'\frac{\partial [C_{Ns}]}{\partial [C_j]} =' + latex(
        Eq(dCnsdCj_orig, dCnsdCj)))

    dCnsdCj_pow = diff(Cns**nu_f[Ns, i], Ck[j])
    write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj_pow))

    dCnsdCj_pow = simplify(assert_subs(dCnsdCj_pow, (Cns, Ck[Ns]),
        (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1)))
    write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial [C_j]} =' + latex(
        dCnsdCj_pow))
    if not conp:
        dCnsdCj_pow = simplify(assert_subs(dCnsdCj_pow, (diff(P, Ck[j]), dPdCj)))
        write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{k, i}}}{\partial [C_j]} =' + latex(
            dCnsdCj_pow))

    def __mod_prod_sum(kval, fwd=True):
        nuv = nu_f if fwd else nu_r
        if kval == Ns:
            return Product(Ck[l]**nuv[l, i], (l, 1, Ns - 1))
        else:
            return Product(Ck[l]**nuv[l, i], (l, 1, kval - 1), (l, kval + 1, Ns))

    def __inner_func(kval, fwd=True):
        nuv = nu_f if fwd else nu_r
        return nuv[kval, i] * Ck[kval] ** (nuv[kval, i] - 1) * __mod_prod_sum(kval, fwd)

    def __create_dRopdCj(fwd=True):
        krate = kf_sym[i] if fwd else kr_sym[i]
        return krate * Sum((dCkdCj + dCnsdCj * KroneckerDelta(k, Ns)) *\
               __inner_func(k, fwd), (k, 1, Ns))

    dRopfdCj = __create_dRopdCj()
    write_eq(diff(Ropf_sym[i], Ck[j]), dRopfdCj)

    dRopfdCj = assert_subs(expand(dRopfdCj, power_base=False, power_exp=False),
        (Sum(KroneckerDelta(Ns, k) * __inner_func(k, True), (k, 1, Ns)),
            __inner_func(Ns, True)),
        (Sum(KroneckerDelta(k, j) * __inner_func(k, True), (k, 1, Ns)),
            __inner_func(j, True))
        )

    dRopfdCj = simplify(dRopfdCj)
    write_eq(diff(Ropf_sym[i], Ck[j]), dRopfdCj)

    #define the S terms
    Sfwd = IndexedBase(r'S^{\prime}')
    write_eq(Sfwd[l], __inner_func(l, True))
    register_equal(Sfwd[j], __inner_func(j, True))
    register_equal(Sfwd[Ns], __inner_func(Ns, True))
    #and sub in
    dRopfdCj = assert_subs(dRopfdCj, (__inner_func(j, True),
        Sfwd[j]), (__inner_func(Ns, True), Sfwd[Ns]))
    write_eq(diff(Ropf_sym[i], Ck[j]), dRopfdCj)
    register_equal(diff(Ropf_sym[i], Ck[j]), dRopfdCj)

    dRoprdCj = __create_dRopdCj(False)
    write_eq(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    dRoprdCj = assert_subs(expand(dRoprdCj, power_base=False, power_exp=False),
        (Sum(KroneckerDelta(Ns, k) * __inner_func(k, False), (k, 1, Ns)),
            __inner_func(Ns, False)),
        (Sum(KroneckerDelta(k, j) * __inner_func(k, False), (k, 1, Ns)),
            __inner_func(j, False))
        )

    dRoprdCj = simplify(dRoprdCj)
    write_eq(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    #define the S terms
    Srev = IndexedBase(r'S^{\prime\prime}')
    write_eq(Srev[l], __inner_func(l, False))
    register_equal(Srev[j], __inner_func(j, False))
    register_equal(Srev[Ns], __inner_func(Ns, False))
    #and sub in
    dRoprdCj = assert_subs(dRoprdCj, (__inner_func(j, False),
        Srev[j]), (__inner_func(Ns, False), Srev[Ns]))
    write_eq(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    register_equal(diff(Ropr_sym[i], Ck[j]), dRoprdCj)

    file.write('For all reversible reactions\n')
    #now do dRop/dCj
    dRopdCj = assert_subs(diff(Rop, Ck[j]),
        (diff(Ropf_sym[i], Ck[j]), dRopfdCj),
        (diff(Ropr_sym[i], Ck[j]), dRoprdCj))
    register_equal(diff(Rop_sym[i], Ck[j]), dRopdCj)
    write_eq(diff(Rop_sym[i], Ck[j]), dRopdCj)

    write_section('Temperature Derivative', sub=True)

    write_eq(Ropf_sym, Ropf)
    dkfdT = assert_subs(factor_terms(diff(kf, T)), (kf, kf_sym[i]))
    write_eq(diff(kf_sym[i], T), dkfdT)
    register_equal(diff(kf_sym[i], T), dkfdT)


    def get_dr_dt(fwd=True, explicit=True, writetofile=True,
                    plog=False, cheb=False):
        Ropt_sym = Ropf_sym if fwd else Ropr_sym
        Rop_temp = Ropf if fwd else Ropr
        nuv = nu_f if fwd else nu_r
        Sval = Sfwd if fwd else Srev

        #sub in Cns for proper temperature derivative
        Rop_temp = assert_subs(Rop_temp, (Product(Ck[k]**nuv[k, i], (k, 1, Ns)),
            Cns**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))))

        if writetofile:
            write_eq(Ropt_sym, Rop_temp)

        dRoptdT = diff(Rop_temp, T)
        if writetofile:
            write_eq(diff(Ropt_sym, T), dRoptdT)

        #sub in Ck[Ns]
        dRoptdT = expand_mul(simplify(assert_subs(dRoptdT, (Cns, Ck[Ns]))))

        #and go back original product
        dRoptdT = assert_subs(dRoptdT, (Ck[Ns] * Ck[Ns]**(nuv[Ns, i] - 1), Ck[Ns]**nuv[Ns, i]))
        dRoptdT = assert_subs(dRoptdT, (Ck[Ns]**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
            Product(Ck[k]**nuv[k, i], (k, 1, Ns))))

        #and sub in C
        dRoptdT = assert_subs(dRoptdT, (Ctot, Ctot_sym))

        if writetofile:
            write_eq(diff(Ropt_sym, T), dRoptdT)

        #finally sub in the S term
        #need to modify the inner function to use k as the sum variable
        inner = __inner_func(Ns, fwd=fwd)

        #make sure it's equivalent before we mess with it
        assert_subs(dRoptdT,
            (inner, Sval[Ns]))

        #switch the sum variable
        inner = assert_subs(inner,
            (__mod_prod_sum(Ns, fwd=fwd),
                Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))))
        #and force a subsitution
        dRoptdT = assert_subs(dRoptdT,
            (inner, Sval[Ns]),
            assumptions=[(inner, Sval[Ns])])

        ksym = kf_sym if fwd else kr_sym
        if fwd:
            if plog:
                dkdT = dkf_pdepdT
            elif cheb:
                dkdT = dkf_chebdT
            else:
                dkdT = dkfdT
        else:
            if plog:
                dkdT = dkr_pdepdT
            elif cheb:
                dkdT = dkr_chebdT
            else:
                dkdT = dkr_rexpdT if explicit else dkrdT

        dRoptdT = assert_subs(dRoptdT, (diff(ksym[i], T), dkdT),
            (Ropf if fwd else Ropr, Ropt_sym[i]),
            assumptions=[(diff(ksym[i], T), dkdT)])

        write_eq(diff(Ropt_sym[i], T), dRoptdT)
        register_equal(diff(Ropt_sym[i], T), dRoptdT)

        return dRoptdT

    dRopfdT = get_dr_dt()

    file.write('For reactions with explicit reverse Arrhenius coefficients\n')

    #set up the correct variables
    A_rexp = IndexedBase(r'{A_{r}}')
    Beta_rexp = IndexedBase(r'{\beta_r}')
    Ea_rexp = IndexedBase(r'{E_{a,r}}')
    kr_rexp = A_rexp[i] * T**Beta_rexp[i] * exp(-Ea_rexp[i] / (R * T))
    Ropr_rexp = kr_rexp * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    register_equal(Ropr_rexp, Ropr_sym[i])

    #find the reverse derivative
    dkr_rexpdT = assert_subs(factor_terms(diff(kr_rexp, T)), (kr_rexp, kr_sym[i]),
        assumptions=[(kr_rexp, kr_sym[i])])

    #and the derivative of Rop
    dRopr_rexpdT = get_dr_dt(fwd=False, explicit=True, writetofile=False)

    dRop_expdT = dRopfdT - dRopr_rexpdT
    dRop_expdT = assert_subs(dRop_expdT, (Ropf, Ropf_sym[i]))

    write_eq(diff(Rop_sym[i], T), dRop_expdT)

    file.write('For non-explicit reversible reactions\n')

    def get_dkr_dT(dkfdTval, writetofile=True):
        #find dkr/dT
        dkrdT = diff(kf_sym[i] / Kc_sym[i], T)
        if writetofile:
            write_eq(diff(kr_sym[i], T), dkrdT)
        dkrdT = assert_subs(dkrdT, (diff(kf_sym[i], T), dkfdTval),
            assumptions=[(diff(kf_sym[i], T), dkfdTval)])
        dkrdT = assert_subs(dkrdT, (kf_sym[i] / Kc_sym[i], kr_sym[i]))
        dkrdT = factor_terms(dkrdT)
        if writetofile:
            write_eq(diff(kr_sym[i], T), dkrdT)

        #dkcdT
        dKcdT = diff(Kc, T)
        dKcdT = assert_subs(dKcdT, (Kc, Kc_sym[i]))
        if writetofile:
            write_eq(diff(Kc_sym[i], T), dKcdT)
            register_equal(diff(Kc_sym[i], T), dKcdT)

        #sub into dkrdT
        dkrdT = assert_subs(dkrdT, (diff(Kc_sym[i], T), dKcdT))
        write_eq(diff(kr_sym[i], T), dkrdT)
        return dkrdT

    dkrdT = get_dkr_dT(dkfdT)
    register_equal(diff(kr_sym[i], T), dkrdT)

    #now the full dRdT
    dRoprdT = get_dr_dt(fwd=False, explicit=False, writetofile=False)

    write_eq(diff(Ropr_sym[i], T), dRoprdT)
    register_equal(diff(Ropr_sym[i], T), dRoprdT)

    dRop_nonexpdT = assert_subs(diff(Rop, T), (diff(Ropf_sym[i], T), dRopfdT),
        (diff(Ropr_sym[i], T), dRoprdT))
    write_eq(diff(Rop_sym[i], T), dRop_nonexpdT)

    write_section(r'Third-Body\slash Falloff Derivatives')
    write_section('Elementary reactions\n', sub=True)
    write_eq(diff(ci[i], T), diff(ci_elem, T))
    write_eq(diff(ci[i], Ck[j]), diff(ci_elem, Ck[j]))

    write_section('Third-body enhanced reactions', sub=True)
    dci_thddT = assert_subs(diff(assert_subs(ci_thd, (Ctot_sym, Ctot)), T),
                                (Ctot, Ctot_sym))
    if not conp:
        dci_thddT = assert_subs(dci_thddT, (diff(P, T), dPdT),
                                            (Ctot, Ctot_sym))
    write_eq(diff(ci_thd_sym, T), dci_thddT)

    dci_thddCj = diff(assert_subs(ci_thd, (Ctot_sym, Ctot)), Ck[j])
    dci_thddCj = assert_subs(dci_thddCj,
            (Sum((-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i]) *
                KroneckerDelta(j, k), (k, 1, Ns - 1)),
            -thd_bdy_eff[Ns, i] + thd_bdy_eff[j, i]))
    write_eq(diff(ci_thd_sym, Ck[j]), dci_thddCj)
    if not conp:
        dci_thddCj = assert_subs(simplify(dci_thddCj), (diff(P, Ck[j]), dPdCj))
        write_eq(diff(ci_thd_sym, Ck[j]), dci_thddCj)
    register_equal(diff(ci_thd_sym, Ck[j]), dci_thddCj)

    file.write(r'For species $m$ as the third-body' + '\n')
    dci_spec_dT = diff(Ck[m], T) * (1 - KroneckerDelta(m, Ns)) + KroneckerDelta(m, Ns) *\
                        assert_subs(diff(Cns, T), (Ctot, Ctot_sym))
    if not conp:
        dci_spec_dT = assert_subs(dci_spec_dT, (diff(P, Ck[j]), dPdCj))

    write_eq(diff(ci[i], T), dci_spec_dT)

    dci_spec_dCj = diff(Ck[m], Ck[j]) * (1 - KroneckerDelta(m, Ns)) + KroneckerDelta(m, Ns) *\
                        dCnsdCj

    write_eq(diff(ci[i], Ck[j]), dci_spec_dCj)


    file.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    dci_unity_dT = assert_subs(diff(Ctot, T),
                                (Ctot, Ctot_sym))
    if not conp:
        dci_unity_dT = assert_subs(dci_unity_dT, (diff(P, T), dPdT),
                                                (Ctot, Ctot_sym))
    write_eq(diff(ci_thd_sym, T), dci_unity_dT)

    dci_unity_dCj = diff(Ctot, Ck[j])
    write_eq(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)
    if not conp:
        dci_unity_dCj = assert_subs(dci_unity_dCj, (diff(P, Ck[j]), dPdCj))
        write_eq(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)
    register_equal(diff(ci_thd_sym, Ck[j]), dci_unity_dCj)

    write_section('Unimolecular/recombination fall-off reactions', sub=True)
    dci_falldT = factor_terms(
        collect(
            assert_subs(diff(ci_fall, T),
                        (ci_fall, ci[i]),
                        assumptions=[(ci_fall, ci[i])]),
        diff(Pri_sym, T)))
    write_eq(diff(ci[i], T), dci_falldT)


    dci_falldCj = factor_terms(
        collect(
            assert_subs(diff(ci_fall, Ck[j]),
                (ci_fall, ci[i]),
                assumptions=[(ci_fall, ci[i])])
            , diff(Pri_sym, Ck[j]) / (Pri_sym + 1)))
    write_eq(diff(ci[i], Ck[j]), dci_falldCj)

    write_section('Chemically-activated bimolecular reactions', sub=True)
    dci_chemdT = factor_terms(
        collect(
            assert_subs(diff(ci_chem, T), (ci_chem, ci[i]),
                assumptions=[(ci_chem, ci[i])]),
            diff(Pri_sym, T)))
    write_eq(diff(ci[i], T), dci_chemdT)

    dci_chemdCj = factor_terms(
        collect(
            assert_subs(diff(ci_chem, Ck[j]), (ci_chem, ci[i]),
                assumptions=[(ci_chem, ci[i])]),
            diff(Pri_sym, Ck[j]) / (Pri_sym + 1)))
    write_eq(diff(ci[i], Ck[j]), dci_chemdCj)

    write_section(r'Reduced Pressure derivatives', sub=True)
    dPri_mixdT = assert_subs(diff(Pri_mix, T), (diff(ci_thd_sym, T), dci_thddT),
        assumptions=[(diff(ci_thd_sym, T), dci_thddT)])
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

    def __get_pri_fac_terms(dPri_dT, dPri_dCj, descriptor):
        #simplify the dPri/dT term
        #find terms with Pr in them
        dPri_dT_prifac = Add(*[x for x in Add.make_args(dPri_dT) if x.has(Pri_sym)])
        dPri_dT_prifac = dPri_dT_prifac / Pri_sym
        dPri_dT_prifac_sym = Symbol(r'\Theta_{{P_{{r,i}}, \partial T, {}}}'.format(descriptor))
        register_equal(dPri_dT_prifac_sym, dPri_dT_prifac)

        #and the non Pr terms
        dPri_dT_noprifac = Add(*[x for x in Add.make_args(dPri_dT) if not x.has(Pri_sym)])
        dPri_dT_noprifac_sym = Symbol(r'\bar{{\theta}}_{{P_{{r, i}}, \partial T, {}}}'.format(descriptor))
        register_equal(dPri_dT_noprifac_sym, dPri_dT_noprifac)

        #now do the dPri/dCj term
        dPri_dCj_fac = dPri_dCj / (k0_sym / kinf_sym)
        dPri_dCj_fac_sym = Symbol(r'\bar{{\theta}}_{{P_{{r, i}}, \partial [C][j], {}}}'.format(descriptor))
        register_equal(dPri_dCj_fac_sym, dPri_dCj_fac)

        #and sub in
        dPri_dT = assert_subs(dPri_dT, (dPri_dT_prifac, dPri_dT_prifac_sym),
            (dPri_dT_noprifac, dPri_dT_noprifac_sym))
        dPri_dCj = assert_subs(dPri_dCj, (dPri_dCj_fac, dPri_dCj_fac_sym))

        #write the substituted forms
        write_eq(diff(Pri_sym, T), dPri_dT)
        write_eq(diff(Pri_sym, Ck[j]), dPri_dCj)

        write_eq(dPri_dT_prifac_sym, dPri_dT_prifac)
        write_eq(dPri_dT_noprifac_sym, dPri_dT_noprifac)
        write_eq(dPri_dCj_fac_sym, dPri_dCj_fac)


        return dPri_dT, dPri_dT_prifac, dPri_dT_prifac_sym, dPri_dT_noprifac, dPri_dT_noprifac_sym,\
            dPri_dCj, dPri_dCj_fac, dPri_dCj_fac_sym

    file.write('\nFor the mixture as the third body\n')
    dPri_mixdT = assert_subs(dPri_mixdT, (diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT))
    dPri_mixdT = assert_subs(collect(dPri_mixdT, Pri_mix / T), (Pri_mix, Pri_sym),
        assumptions=[(Pri_mix, Pri_sym)])
    write_eq(diff(Pri_sym, T), dPri_mixdT)

    dPri_mixdCj = assert_subs(diff(Pri_mix, Ck[j]), (diff(ci_thd_sym, Ck[j]), dci_thddCj))
    dPri_mixdCj = assert_subs(dPri_mixdCj, (Sum((-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i])
            * KroneckerDelta(j, k), (k, 1, Ns - 1)),
        -thd_bdy_eff[Ns, i] + thd_bdy_eff[j, i]))
    write_eq(diff(Pri_sym, Ck[j]), dPri_mixdCj)

    file.write('Simplifying:\n')
    dPri_mixdT, dPri_mixdT_prifac, dPri_mixdT_prifac_sym, dPri_mixdT_noprifac, dPri_mixdT_noprifac_sym,\
            dPri_mixdCj, dPri_mixdCj_fac, dPri_mixdCj_fac_sym = __get_pri_fac_terms(dPri_mixdT, dPri_mixdCj, "mix")

    file.write('For species $m$ as the third-body\n')

    dPri_specdT = diff(Pri_spec, T)
    dPri_specdT = assert_subs(dPri_specdT, (diff(k0_sym, T), dk0dT),
        (diff(kinf_sym, T), dkinfdT))
    dPri_specdT = assert_subs(collect(dPri_specdT, Pri_spec / T), (Pri_spec, Pri_sym),
        assumptions=[(Pri_spec, Pri_sym)])
    write_eq(diff(Pri_sym, T), dPri_specdT)

    dCmdCj = (1 - KroneckerDelta(m, Ns)) * diff(Ck[m], Ck[j]) + KroneckerDelta(m, Ns) * dCnsdCj
    register_equal(diff(Ck[m], Ck[j]), dCmdCj)
    dPri_specdCj = assert_subs(diff(Pri_spec, Ck[j]), (diff(Ck[m], Ck[j]), dCmdCj))
    write_eq(diff(Pri_sym, Ck[j]), dPri_specdCj)

    file.write('Simplifying:\n')
    dPri_specdT, dPri_specdT_prifac, dPri_specdT_prifac_sym, dPri_specdT_noprifac, dPri_specdT_noprifac_sym,\
            dPri_specdCj, dPri_specdCj_fac, dPri_specdCj_fac_sym = __get_pri_fac_terms(dPri_specdT, dPri_specdCj, "spec")

    file.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
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
    write_eq(diff(Pri_sym, T), dPri_unitydT)

    if not conp:
        dPri_unitydT = assert_subs(dPri_unitydT, (diff(P, T), dPdT),
            (Pri_unity, Pri_sym),
            assumptions=[(Pri_unity, Pri_sym)])
        dPri_unitydT = collect(dPri_unitydT, Pri_sym / T)
        write_eq(diff(Pri_sym, T), dPri_unitydT)

    dPri_unitydCj = diff(Pri_unity, Ck[j])
    write_eq(diff(Pri_sym, Ck[j]), dPri_unitydCj)

    if not conp:
        dPri_unitydCj = assert_subs(dPri_unitydCj, (diff(P, Ck[j]), dPdCj))
        write_eq(diff(Pri_sym, Ck[j]), dPri_unitydCj)

    file.write('Simplifying:\n')
    dPri_unitydT, dPri_unitydT_prifac, dPri_unitydT_prifac_sym, dPri_unitydT_noprifac, dPri_unitydT_noprifac_sym,\
            dPri_unitydCj, dPri_unitydCj_fac, dPri_unitydCj_fac_sym = __get_pri_fac_terms(dPri_unitydT, dPri_unitydCj, "unity")

    #finally we make a generic version for simplification
    file.write('Thus we write:\n')
    dPri_dT_prifac_sym = Symbol(r'\Theta_{P_{r,i}, \partial T}')
    dPri_dT_noprifac_sym = Symbol(r'\bar{\theta}_{P_{r, i}, \partial T}')
    dPri_dCj_fac_sym = Symbol(r'\bar{\theta}_{P_{r, i}, \partial [C][j]}')
    dPri_dT = assert_subs(dPri_mixdT, (dPri_mixdT_prifac_sym, dPri_dT_prifac_sym),
        (dPri_mixdT_noprifac_sym, dPri_dT_noprifac_sym),
        assumptions=[(dPri_mixdT_prifac_sym, dPri_dT_prifac_sym),
        (dPri_mixdT_noprifac_sym, dPri_dT_noprifac_sym)])
    dPri_dCj = assert_subs(dPri_mixdCj, (dPri_mixdCj_fac_sym, dPri_dCj_fac_sym),
        assumptions=[(dPri_mixdCj_fac_sym, dPri_dCj_fac_sym)])

    write_eq(diff(Pri_sym, T), dPri_dT)
    write_eq(diff(Pri_sym, Ck[j]), dPri_dCj)
    register_equal(diff(Pri_sym, T), dPri_dT)
    register_equal(diff(Pri_sym, Ck[j]), dPri_dCj)

    file.write('For\n')
    write_cases(dPri_dT_prifac_sym, [(dPri_mixdT_prifac, "mix"),
        (dPri_specdT_prifac, "species"),
        (dPri_unitydT_prifac, "unity")])
    write_cases(dPri_dT_noprifac_sym, [(dPri_mixdT_noprifac, "mix"),
        (dPri_specdT_noprifac, "species"),
        (dPri_unitydT_noprifac, "unity")])
    write_cases(dPri_dCj_fac_sym, [(dPri_mixdCj_fac, "mix"),
        (dPri_specdCj_fac, "species"),
        (dPri_unitydCj_fac, "unity")])

    write_section('Falloff Blending Factor derivatives', sub=True)
    file.write('\n For Lindemann reactions\n')

    dFi_linddT = diff(Fi_lind, T)
    dFi_linddCj = diff(Fi_lind, Ck[j])
    write_conditional(diff(Fi_sym, T), dFi_linddT, enum_conds=falloff_form.lind)
    write_conditional(diff(Fi_sym, Ck[j]), dFi_linddCj, enum_conds=falloff_form.lind)

    file.write('For Troe reactions\n')
    dFi_troedT = diff(Fi_troe_sym, T)
    dFi_troedCj = diff(Fi_troe_sym, Ck[j])
    write_conditional(diff(Fi_sym, T), dFi_troedT, enum_conds=falloff_form.troe)
    write_conditional(diff(Fi_sym, Ck[j]), dFi_troedCj, enum_conds=falloff_form.troe)

    file.write('where\n')
    troe_collect_poly = 2 * Atroe_sym / (Btroe_sym**3)
    dFi_troedFcent = assert_subs(factor_terms(
        diff(Fi_troe, Fcent_sym)), (Fi_troe, Fi_troe_sym))
    write_eq(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent,
        register_equal=True, sympy=True)

    dFcentdT = diff(Fcent, T)
    write_eq(diff(Fcent_sym, T), dFcentdT)
    register_equal(diff(Fcent_sym, T), dFcentdT)

    dFi_troedPri = factor_terms(
        assert_subs(diff(Fi_troe, Pri_sym),
            (Fi_troe, Fi_troe_sym)))
    write_eq(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    file.write('And\n')
    dAtroedFcent = diff(Atroe, Fcent_sym)
    dBtroedFcent = diff(Btroe, Fcent_sym)
    dAtroedPri = diff(Atroe, Pri_sym)
    dBtroedPri = diff(Btroe, Pri_sym)
    write_eq(diff(Atroe_sym, Fcent_sym), dAtroedFcent)
    register_equal(diff(Atroe_sym, Fcent_sym), dAtroedFcent)

    write_eq(diff(Btroe_sym, Fcent_sym), dBtroedFcent)
    register_equal(diff(Btroe_sym, Fcent_sym), dBtroedFcent)

    write_eq(diff(Atroe_sym, Pri_sym), dAtroedPri)
    register_equal(diff(Atroe_sym, Pri_sym), dAtroedPri)

    write_eq(diff(Btroe_sym, Pri_sym), dBtroedPri)
    register_equal(diff(Btroe_sym, Pri_sym), dBtroedPri)

    file.write('Thus\n')
    dFi_troedFcent = factor_terms(simplify(
            assert_subs(dFi_troedFcent,
            (diff(Atroe_sym, Fcent_sym), dAtroedFcent),
            (diff(Btroe_sym, Fcent_sym), dBtroedFcent)
            )))
    write_eq(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)
    register_equal(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent)

    dFi_troedPri = factor_terms(
        assert_subs(dFi_troedPri,
            (diff(Atroe_sym, Pri_sym), dAtroedPri),
            (diff(Btroe_sym, Pri_sym), dBtroedPri))
        )
    write_eq(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)
    register_equal(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    file.write('And\n')
    dFi_troedT = assert_subs(dFi_troedT, (diff(Fi_troe_sym, Pri_sym), dFi_troedPri),
        (diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent),
        (diff(Pri_sym, T), dPri_dT))
    dFi_troedT = simplify(dFi_troedT)

    dFi_troedT_fac = dFi_troedT / Fi_troe_sym

    #used many places
    dFi_dT_fac_sym = Symbol(r'\Theta_{F_i, \partial T}')
    dFi_dCj_fac_sym = Symbol(r'\Theta_{F_i, \partial [C][j]}')

    dFi_troedT = assert_subs(dFi_troedT, (dFi_troedT_fac, dFi_dT_fac_sym),
        assumptions=[(dFi_troedT_fac, dFi_dT_fac_sym)])
    write_eq(diff(Fi_sym, T), dFi_troedT)

    dFi_troedCj = assert_subs(dFi_troedCj, (diff(Fi_troe_sym, Pri_sym), dFi_troedPri),
        (diff(Pri_sym, Ck[j]), dPri_dCj))
    dFi_troedCj = simplify(dFi_troedCj)
    dFi_troedCj_fac = dFi_troedCj / Fi_troe_sym

    dFi_troedCj = assert_subs(dFi_troedCj, (dFi_troedCj_fac, dFi_dCj_fac_sym),
        assumptions=[(dFi_troedCj_fac, dFi_dCj_fac_sym)])
    write_eq(diff(Fi_sym, Ck[j]), dFi_troedCj)

    file.write('Where\n')
    write_eq(dFi_dT_fac_sym, dFi_troedT_fac)
    write_eq(dFi_dCj_fac_sym, dFi_troedCj_fac)

    file.write('For SRI reactions\n')
    dFi_sridT = factor_terms(
        assert_subs(diff(Fi_sri, T), (Fi_sri, Fi_sym)))
    dFi_sridCj = assert_subs(diff(Fi_sri, Ck[j]),
        (Fi_sri, Fi_sym))
    write_eq(diff(Fi_sym, T), dFi_sridT)
    write_eq(diff(Fi_sym, Ck[j]), dFi_sridCj)

    file.write('Where\n')
    dXdPri = assert_subs(diff(X, Pri_sym), (X, X_sym))
    write_eq(diff(X_sym, Pri_sym), dXdPri)
    register_equal(diff(X_sym, Pri_sym), dXdPri)

    write_eq(r'\frac{\partial X}{\partial [C]_j} = ' + latex(diff(X_sym, Ck[j])))

    file.write('And\n')
    dFi_sridT = simplify(
        assert_subs(dFi_sridT, (diff(X_sym, Pri_sym), dXdPri),
        (diff(Pri_sym, T), dPri_dT)))

    dFi_sridT_fac = dFi_sridT / Fi_sym
    dFi_sridT = assert_subs(dFi_sridT, (dFi_sridT_fac, dFi_dT_fac_sym),
        assumptions=[(dFi_sridT_fac, dFi_dT_fac_sym)])
    write_eq(diff(Fi_sym, T), dFi_sridT)

    dFi_sridCj = simplify(
            assert_subs(dFi_sridCj, (diff(X_sym, Pri_sym), dXdPri),
            (diff(Pri_sym, Ck[j]), dPri_dCj)))

    dFi_sridCj_fac = dFi_sridCj / Fi_sym
    dFi_sridCj = assert_subs(dFi_sridCj, (dFi_sridCj_fac, dFi_dCj_fac_sym),
        assumptions=[(dFi_sridCj_fac, dFi_dCj_fac_sym)])
    write_eq(diff(Fi_sym, Ck[j]), dFi_sridCj)

    file.write('Where\n')
    write_eq(dFi_dT_fac_sym, dFi_sridT_fac)
    write_eq(dFi_dCj_fac_sym, dFi_sridCj_fac)

    file.write('Simplifying:\n')
    dFi_dT = assert_subs(dFi_troedT,
        (Fi_troe_sym, Fi_sym),
        assumptions=[(Fi_troe_sym, Fi_sym)])
    write_eq(diff(Fi_sym, T), dFi_dT)
    register_equal(diff(Fi_sym, T), dFi_dT)

    dFi_dCj = assert_subs(dFi_troedCj,
        (Fi_troe_sym, Fi_sym),
        assumptions=[(Fi_troe_sym, Fi_sym)])
    write_eq(diff(Fi_sym, Ck[j]), dFi_dCj)
    register_equal(diff(Fi_sym, Ck[j]), dFi_dCj)

    file.write('Where:\n')

    dFi_linddT_fac = dFi_linddT / Fi_sym
    write_cases(dFi_dT_fac_sym, [(dFi_linddT_fac, 'Lindemann'),
        (dFi_troedT_fac, 'Troe'),
        (dFi_sridT_fac, 'SRI')])

    dFi_linddCj_fac = dFi_linddCj / Fi_sym
    write_cases(dFi_dCj_fac_sym, [(dFi_linddCj_fac, 'Lindemann'),
        (dFi_troedCj_fac, 'Troe'),
        (dFi_sridCj_fac, 'SRI')])

    write_section('Unimolecular/recombination fall-off reactions (complete)', sub=True)
    def __subs_ci_terms(dci_dT, dci_dCj, ci_term):
        dci_dT = assert_subs(expand(
                assert_subs(dci_dT,
                (diff(Fi_sym, T), dFi_dT),
                (diff(Pri_sym, T), dPri_dT))),
            (ci_term, ci[i]),
            assumptions=[(ci_term, ci[i])])
        dci_dT = factor_terms(collect(dci_dT,
            [ci[i], Pri_sym]))

        dci_dCj = assert_subs(expand(assert_subs(dci_dCj,
                (diff(Fi_sym, Ck[j]), dFi_dCj),
                (diff(Pri_sym, Ck[j]), dPri_dCj))),
            (ci_term, ci[i]),
            assumptions=[(ci_term, ci[i])])
        dci_dCj = factor_terms(collect(dci_dCj,
            [ci[i], Pri_sym]))
        write_eq(diff(ci[i], T), dci_dT)
        write_eq(diff(ci[i], Ck[j]), dci_dCj)
        return dci_dT, dci_dCj

    dci_falldT, dci_falldCj = __subs_ci_terms(dci_falldT, dci_falldCj, ci_fall)

    write_section('Chemically-activated bimolecular reactions (complete)', sub=True)

    dci_chemdT, dci_chemdCj = __subs_ci_terms(dci_chemdT, dci_chemdCj, ci_chem)

    write_section('Pressure-dependent reaction derivatives')
    file.write('For PLog reactions\n')
    dkf_pdepdT = diff(kf_pdep, T)
    #since the kf_pdep is expressed as a log
    #we need to solve for this in terms of dkf/dT
    mul_term = diff(kf_sym[i], T) / diff(log(kf_sym[i]), T)
    dkf_pdepdT = dkf_pdepdT * mul_term
    write_eq(diff(kf_sym[i], T), dkf_pdepdT)
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
    write_eq(diff(kf_sym[i], T), dkf_pdepdT)

    #and even futher
    dkf_pdepdT = factor_terms(dkf_pdepdT)
    write_eq(diff(kf_sym[i], T), dkf_pdepdT)

    #assemble the Rop derivatives
    dRopf_pdepdT = get_dr_dt(plog=True, writetofile=False)
    dkr_pdepdT = get_dkr_dT(dkf_pdepdT, writetofile=False)
    dRopr_pdepdT = get_dr_dt(plog=True, fwd=False, writetofile=False)
    dRop_pdepdT = dRopf_pdepdT - dRopr_pdepdT

    #transfer dkf_pdepdT / kf_sym for a temporary variable for simplification
    def __complex_collect(obj, term_list, expand=False):
        if not isinstance(term_list, list):
            term_list = [term_list]
        temp_syms = [Symbol('temp{}'.format(i)) for i in range(len(term_list))]
        temp = Symbol('temp')
        cobj = assert_subs(obj,
            *[(term_list[i], temp_syms[i]) for i in range(len(term_list))],
            assumptions=[(term_list[i], temp_syms[i]) for i in range(len(term_list))])
        if expand:
            cobj = factor_terms(collect(expand_mul(cobj), temp_syms))
        else:
            cobj = collect(cobj, temp_syms)
        return assert_subs(cobj,
            *[(temp_syms[i], term_list[i]) for i in range(len(term_list))],
            assumptions=[(temp_syms[i], term_list[i]) for i in range(len(term_list))])

    dRop_pdepdT = __complex_collect(dRop_pdepdT, dkf_pdepdT / kf_sym[i])
    dRop_pdepdT = collect(dRop_pdepdT, Ctot_sym / T)
    write_eq(diff(Rop_sym[i], T), dRop_pdepdT)

    file.write('For Chebyshev reactions\n')
    dkf_chebdT = diff(kf_cheb, T) * mul_term
    write_eq(diff(kf_sym[i], T), dkf_chebdT)
    dkf_chebdT = assert_subs(dkf_chebdT, (diff(Tred_sym, T), diff(Tred, T)))
    write_eq(diff(kf_sym[i], T), dkf_chebdT)

    if not conp:
        dkf_chebdT = assert_subs(dkf_chebdT,
                        (diff(Pred_sym, T), diff(Pred, T)),
                        (diff(P, T), dPdT))
        dkf_chebdT = factor_terms(dkf_chebdT)
        write_eq(diff(kf_sym[i], T), dkf_chebdT)

    #assemble the Rop derivatives
    dRopf_chebdT = get_dr_dt(cheb=True, writetofile=False)
    dkr_chebdT = get_dkr_dT(dkf_chebdT, writetofile=False)
    dRopr_chebdT = get_dr_dt(cheb=True, fwd=False, writetofile=False)
    dRop_chebdT = dRopf_chebdT - dRopr_chebdT
    #do the same trick as for plog, where we sub out for a temporary variable
    dRop_chebdT = __complex_collect(dRop_chebdT, dkf_chebdT / kf_sym[i])
    dRop_chebdT = collect(dRop_chebdT, Ctot_sym / T)
    write_eq(diff(Rop_sym[i], T), dRop_chebdT)

    write_section('Jacobian entries')
    write_section('Energy Equation', sub=True)

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

    write_section(r'\texorpdfstring{$\dot{T}$}{dTdt} Derivatives', subsub=True)
    file.write('Concentration derivative\n')
    #first we do the concentration derivative
    dTdotdC_sym = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    dTdotdC = simplify(diff(dTdt, Ck[j]))
    write_eq(dTdotdC_sym, dTdotdC)

    if not conp:
        dTdotdC = assert_subs(dTdotdC, (diff(Ctot_sym, P), diff(Ctot, P)),
            (diff(P, Ck[j]), dPdCj),
            assumptions=[(diff(Ctot_sym, P), diff(Ctot, P))])
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
    dTdotdT = assert_subs(dTdotdT, (Ctot, Ctot_sym))
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

    write_section(r'\texorpdfstring{$\dot{C_k}$}{dCkdt} Derivatives', subsub=True)

    #concentration Jacobian equations
    dCdot = MyIndexedFunc(r'\dot{C}', (Ck, T))
    write_eq(diff(dCdot[k], Ck[j]), diff(omega_sym[k], Ck[j]))
    write_eq(diff(dCdot[k], T), diff(omega_sym[k], T))

    write_section('Jacobian Update Form')
    write_section('Temperature Derivatives', sub=True)

    domegadT = diff(omega_k, T)
    domegadCj = diff(omega_k, Ck[j])

    write_eq(Eq(Jac[k + 1, 1], diff(omega_sym[k], T)), domegadT)
    write_eq(Eq(Jac[k + 1, j + 1], diff(omega_sym[k], Ck[j])), domegadCj)

    file.write('Converting to update form:\n')
    domegadT = domegadT.function
    domegadCj = domegadCj.function

    write_dummy_eq(latex(Jac[k + 1, 1]) + r'\pluseq' + latex(domegadT) + r'\text{\quad} k = 1, \ldots, N_{sp} - 1')
    write_dummy_eq(latex(Jac[k + 1, j + 1]) + r'\pluseq' + latex(domegadCj) + r'\text{\quad} k,j = 1, \ldots, N_{sp} - 1')

    dRopdT_temp = Symbol(r'\Theta_{\partial T, i}')

    dqdT = assert_subs(diff(q, T), (diff(Rop_sym[i], T), dRopdT_temp),
        assumptions=[(diff(Rop_sym[i], T), dRopdT_temp)])

    write_section('Explicit reversible reactions', subsub=True)
    write_eq(diff(q_sym[i], T), dqdT)
    write_eq(dRopdT_temp, dRop_expdT)

    write_section('Non-explicit reversible reactions', subsub=True)
    write_eq(diff(q_sym[i], T), dqdT)
    write_eq(dRopdT_temp, dRop_nonexpdT)

    write_section('Pressure-dependent reactions', subsub=True)

    dqdT_pdep = assert_subs(dqdT,
        (ci[i], ci_elem),
        (diff(ci[i], T), diff(ci_elem, T)),
        assumptions=[(ci[i], ci_elem),
        (diff(ci[i], T), diff(ci_elem, T))])
    write_eq(diff(q_sym[i], T), dqdT_pdep)

    file.write('For PLog reactions:\n')
    write_eq(dRopdT_temp, dRop_pdepdT)
    file.write('For Chebyshev reactions:\n')
    write_eq(dRopdT_temp, dRop_chebdT)

    write_section('Pressure independent reactions', subsub=True)

    dqdT_ind = assert_subs(dqdT,
        (ci[i], ci_elem),
        (diff(ci[i], T), diff(ci_elem, T)),
        assumptions=[(ci[i], ci_elem),
        (diff(ci[i], T), diff(ci_elem, T))])
    write_eq(diff(q_sym[i], T), dqdT_ind)

    write_section('Third-body enhanced reactions', subsub=True)
    file.write('For mixture as third-body:\n')
    dqdT_thd = assert_subs(dqdT,
        (ci[i], ci_thd_sym),
        (diff(ci[i], T), dci_thddT),
        assumptions=[(ci[i], ci_thd_sym),
        (diff(ci[i], T), dci_thddT)])
    write_eq(diff(q_sym[i], T), dqdT_thd)

    file.write('For species $m$ as third-body:\n')
    dqdT_spec_thd = assert_subs(dqdT,
        (ci[i], Ck[m]),
        (diff(ci[i], T), dci_spec_dCj),
        assumptions=[(ci[i], Ck[m]),
        (diff(ci[i], T), dci_spec_dCj)])
    write_eq(diff(q_sym[i], T), dqdT_spec_thd)

    file.write('If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$ for all species j:\n')
    dqdT_unity_thd = assert_subs(dqdT,
        (ci[i], Ctot_sym),
        (diff(ci[i], T), dci_unity_dT),
        assumptions=[(ci[i], Ctot_sym),
        (diff(ci[i], T), dci_unity_dT)])
    dqdT_unity_thd = collect(dqdT_unity_thd, Ctot_sym)
    write_eq(diff(q_sym[i], T), dqdT_unity_thd)

    write_section('Unimolecular\slash recombination fall-off reactions', subsub=True)

    dummy_collector = (Beta_0 - Beta_inf + Ea_0 / (R * T) - Ea_inf / (R * T)) / T
    dqdT_fall_thd = assert_subs(dqdT,
        (diff(ci[i], T), dci_falldT),
        assumptions=[(diff(ci[i], T), dci_falldT)])
    dqdT_fall_thd = collect(dqdT_fall_thd, ci[i])

    write_eq(diff(q_sym[i], T), dqdT_fall_thd)

    def __get_ci_dT(starting_form, pri_fac, no_pri_fac, complex_collector, other_collects, expand=False):
        dci = assert_subs(starting_form,
            (dPri_dT_noprifac_sym, no_pri_fac),
            (dPri_dT_prifac_sym, pri_fac),
            assumptions=[(dPri_dT_noprifac_sym, no_pri_fac),
                (dPri_dT_prifac_sym, pri_fac)])

        dci = __complex_collect(dci, complex_collector, expand=expand)
        dci = collect(dci, other_collects)
        dq = assert_subs(dqdT,
            (diff(ci[i], T), dci),
            assumptions=[(diff(ci[i], T), dci)]
            )
        dq = collect(dq, ci[i])
        write_eq(diff(q_sym[i], T), dq)
        return dci, dq

    file.write(r'\textbf{For mixture as third-body}:' + '\n')
    dci_fallmix_dT, dqdT_fall_mix_thd = __get_ci_dT(dci_falldT, dPri_mixdT_prifac, dPri_mixdT_noprifac,
        dummy_collector, [Ctot_sym * k0_sym * thd_bdy_eff[Ns, i] / (T * kinf_sym * (Pri_sym + 1)), ci[i]], expand=True)

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    dci_fallspec_dT, dqdT_fall_spec_thd = __get_ci_dT(dci_falldT, dPri_specdT_prifac, dPri_specdT_noprifac,
        dummy_collector, [ci[i]])

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    dci_fallunity_dT, dqdT_fall_unity_thd = __get_ci_dT(dci_falldT, dPri_unitydT_prifac, dPri_unitydT_noprifac,
        collect(dummy_collector - 1/T, 1/T), [ci[i]])

    write_section(r'Chemically-activated bimolecular reactions', subsub=True)
    dqdT_chem_thd = assert_subs(dqdT,
        (diff(ci[i], T), dci_chemdT),
        assumptions=[(diff(ci[i], T), dci_chemdT)])
    dqdT_chem_thd = collect(dqdT_chem_thd, ci[i])
    write_eq(diff(q_sym[i], T), dqdT_chem_thd)

    file.write(r'\textbf{For mixture as third-body}:' + '\n')
    dci_chemmix_dT, dqdT_chem_mix_thd = __get_ci_dT(dci_chemdT, dPri_mixdT_prifac, dPri_mixdT_noprifac,
        dummy_collector, [Ctot_sym * k0_sym * thd_bdy_eff[Ns, i] / (T * kinf_sym * (Pri_sym + 1)), ci[i]])

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    dci_chemspec_dT, dqdT_chem_spec_thd = __get_ci_dT(dci_chemdT, dPri_specdT_prifac, dPri_specdT_noprifac,
        dummy_collector, [ci[i]])

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    dci_chemunity_dT, dqdT_chem_unity_thd = __get_ci_dT(dci_chemdT, dPri_unitydT_prifac, dPri_unitydT_noprifac,
        collect(dummy_collector - 1/T, 1/T), [ci[i]])

    write_section('Falloff Blending Function Forms', subsub=True)
    def __get_fi_dT(starting_form, pri_fac, no_pri_fac, fi_fac):
        dfi = assert_subs(starting_form,
            (dFi_dT_fac_sym, fi_fac),
            (dPri_dT_prifac_sym, pri_fac),
            (dPri_dT_noprifac_sym, no_pri_fac),
            assumptions=[(dFi_dT_fac_sym, fi_fac),
            (dPri_dT_prifac_sym, pri_fac),
            (dPri_dT_noprifac_sym, no_pri_fac)])
        write_eq(dFi_dT_fac_sym, dfi)
        return dfi

    file.write(r'\textbf{For mixture as third-body}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddT_mix = __get_fi_dT(dFi_linddT, dPri_mixdT_prifac, dPri_mixdT_noprifac, dFi_linddT_fac)

    file.write('For Troe\n')
    dFi_troedT_mix = __get_fi_dT(dFi_troedT, dPri_mixdT_prifac, dPri_mixdT_noprifac, dFi_troedT_fac)

    file.write('For SRI\n')
    dFi_sridT_mix = __get_fi_dT(dFi_sridT, dPri_mixdT_prifac, dPri_mixdT_noprifac, dFi_sridT_fac)

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddT_spec = __get_fi_dT(dFi_linddT, dPri_specdT_prifac, dPri_specdT_noprifac, dFi_linddT_fac)

    file.write('For Troe\n')
    dFi_troedT_spec = __get_fi_dT(dFi_troedT, dPri_specdT_prifac, dPri_specdT_noprifac, dFi_troedT_fac)

    file.write('For SRI\n')
    dFi_sridT_spec = __get_fi_dT(dFi_sridT, dPri_specdT_prifac, dPri_specdT_noprifac, dFi_sridT_fac)

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddT_unity = __get_fi_dT(dFi_linddT, dPri_unitydT_prifac, dPri_unitydT_noprifac, dFi_linddT_fac)

    file.write('For Troe\n')
    dFi_troedT_unity = __get_fi_dT(dFi_troedT, dPri_unitydT_prifac, dPri_unitydT_noprifac, dFi_troedT_fac)

    file.write('For SRI\n')
    dFi_sridT_unity = __get_fi_dT(dFi_sridT, dPri_unitydT_prifac, dPri_unitydT_noprifac, dFi_sridT_fac)

    write_section('Concentration Derivatives', sub=True)
    domegadCj = diff(omega_k, Ck[j])
    write_eq(Eq(Jac[k + 1, j + 1], diff(omega_sym[k], Ck[j])), domegadCj)

    file.write('Converting to Jacobian Update form:\n')
    domegadCj = domegadCj.function
    write_dummy_eq(latex(Jac[k + 1, j + 1]) + r'\pluseq' + latex(domegadCj))

    dqdCj = diff(q, Ck[j])
    dqdCj = assert_subs(dqdCj,
        (diff(Rop_sym[i], Ck[j]), dRopdCj))
    write_eq(diff(q_sym[k], Ck[j]), dqdCj)

    write_section('Pressure-dependent reactions', subsub=True)

    dqdCj_pdep = assert_subs(dqdCj,
        (ci[i], ci_elem),
        (diff(ci[i], Ck[j]), diff(ci_elem, Ck[j])),
        assumptions=[(ci[i], ci_elem),
        (diff(ci[i], Ck[j]), diff(ci_elem, Ck[j]))])
    write_eq(diff(q_sym[k], Ck[j]), dqdCj_pdep)

    write_section('Pressure independent reactions', subsub=True)

    dqdCj_ind = assert_subs(dqdCj,
        (ci[i], ci_elem),
        (diff(ci[i], Ck[j]), diff(ci_elem, Ck[j])),
        assumptions=[(ci[i], ci_elem),
        (diff(ci[i], Ck[j]), diff(ci_elem, Ck[j]))])
    write_eq(diff(q_sym[k], Ck[j]), dqdCj_ind)

    write_section('Third-body enhanced reactions', subsub=True)

    file.write(r'\textbf{For mixture as third-body}:' + '\n')
    dqdCj_thd = assert_subs(dqdCj,
        (ci[i], ci_thd_sym),
        (diff(ci[i], Ck[j]), dci_thddCj),
        assumptions=[(ci[i], ci_thd_sym),
        (diff(ci[i], Ck[j]), dci_thddCj)]
        )

    write_eq(diff(q_sym[k], Ck[j]), dqdCj_thd)

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    dqdCj_thd_spec = assert_subs(dqdCj,
        (ci[i], Ck[m]),
        (diff(ci[i], Ck[j]), dci_spec_dCj),
        assumptions=[(ci[i], Ck[m]),
        (diff(ci[i], Ck[j]), dci_spec_dCj)]
        )

    write_eq(diff(q_sym[k], Ck[j]), dqdCj_thd_spec)

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    dqdCj_thd_unity = assert_subs(dqdCj,
        (ci[i], Ctot_sym),
        (diff(ci[i], Ck[j]), dci_unity_dCj),
        assumptions=[(ci[i], Ctot_sym),
        (diff(ci[i], Ck[j]), dci_unity_dCj)]
        )

    write_eq(diff(q_sym[k], Ck[j]), dqdCj_thd_unity)

    write_section('Falloff Reactions', subsub=True)
    file.write(r'\textbf{Unimolecular\slash recombination fall-off reactions}:' + '\n')
    def __get_ci_dcj(starting_form, pri_fac, other_collects, complex_collector=None):
        dci = assert_subs(starting_form,
            (dPri_dCj_fac_sym, pri_fac),
            assumptions=[(dPri_dCj_fac_sym, pri_fac)])

        if complex_collector:
            dci = __complex_collect(dci, complex_collector, expand=True)
        dci = collect(dci, other_collects)
        dq = assert_subs(dqdCj,
            (diff(ci[i], Ck[j]), dci),
            assumptions=[(diff(ci[i], Ck[j]), dci)]
            )
        dq = collect(dq, ci[i])
        write_eq(diff(q_sym[i], Ck[j]), dq)
        return dci, dq

    dci_falldCj = __complex_collect(dci_falldCj, k0_sym * dPri_dCj_fac_sym / (kinf_sym * (Pri_sym + 1)), expand=True)
    dqdCj_fall_thd = assert_subs(dqdCj,
        (diff(ci[i], Ck[j]), dci_falldCj),
        assumptions=[(diff(ci[i], Ck[j]), dci_falldCj)])
    dqdCj_fall_thd = collect(dqdCj_fall_thd, ci[i])
    write_eq(diff(q_sym[i], Ck[j]), dqdCj_fall_thd)

    file.write(r'\textbf{For mixture as third-body}:' + '\n')

    dci_fallmix_dCj, dqdCj_fall_mix_thd = __get_ci_dcj(dci_falldCj, dPri_mixdCj_fac, [ci[i]])

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n')

    dci_fallspec_dCj, dqdCj_fall_spec_thd = __get_ci_dcj(dci_falldCj, dPri_specdCj_fac, [ci[i]])

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')

    dci_fallunity_dCj, dqdCj_fall_unity_thd = __get_ci_dcj(dci_falldCj, dPri_unitydCj_fac, [ci[i]])

    write_section('Chemically-activated bimolecular reactions', subsub=True)

    dci_chemdCj = __complex_collect(dci_chemdCj, k0_sym * dPri_dCj_fac_sym / (kinf_sym * (Pri_sym + 1)), expand=True)
    dqdCj_chem_thd = assert_subs(dqdCj,
        (diff(ci[i], Ck[j]), dci_chemdCj),
        assumptions=[(diff(ci[i], Ck[j]), dci_chemdCj)])
    dqdCj_chem_thd = collect(dqdCj_chem_thd, ci[i])
    write_eq(diff(q_sym[i], Ck[j]), dqdCj_chem_thd)

    file.write(r'\textbf{For mixture as third-body}:' + '\n')

    dci_chemmix_dCj, dqdCj_chem_mix_thd = __get_ci_dcj(dci_chemdCj, dPri_mixdCj_fac, [ci[i]])

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n')

    dci_chemspec_dCj, dqdCj_chem_spec_thd = __get_ci_dcj(dci_chemdCj, dPri_specdCj_fac, [ci[i]])

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')

    dci_chemunity_dCj, dqdCj_chem_unity_thd = __get_ci_dcj(dci_chemdCj, dPri_unitydCj_fac, [ci[i]])

    write_section('Falloff Blending Function Forms', subsub=True)
    def __get_fi_dcj(starting_form, pri_fac, fi_fac):
        dfi = assert_subs(starting_form,
            (dFi_dCj_fac_sym, fi_fac),
            (dPri_dCj_fac_sym, pri_fac),
            assumptions=[(dFi_dCj_fac_sym, fi_fac),
            (dPri_dCj_fac_sym, pri_fac)])
        write_eq(dFi_dCj_fac_sym, dfi)
        return dfi

    file.write(r'\textbf{For mixture as third-body}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddCj_mix = __get_fi_dcj(dFi_linddCj, dPri_mixdCj_fac, dFi_linddCj_fac)

    file.write('For Troe\n')
    dFi_troedCj_mix = __get_fi_dcj(dFi_troedCj, dPri_mixdCj_fac, dFi_troedCj_fac)

    file.write('For SRI\n')
    dFi_sridCj_mix = __get_fi_dcj(dFi_sridCj, dPri_mixdCj_fac, dFi_sridCj_fac)

    file.write(r'\textbf{For species $m$ as third-body}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddCj_spec = __get_fi_dcj(dFi_linddCj, dPri_specdCj_fac, dFi_linddCj_fac)

    file.write('For Troe\n')
    dFi_troedCj_spec = __get_fi_dcj(dFi_troedCj, dPri_specdCj_fac, dFi_troedCj_fac)

    file.write('For SRI\n')
    dFi_sridCj_spec = __get_fi_dcj(dFi_sridCj, dPri_specdCj_fac, dFi_sridCj_fac)

    file.write(r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n\n')
    file.write('For Lindemann\n')
    dFi_linddCj_unity = __get_fi_dcj(dFi_linddCj, dPri_unitydCj_fac, dFi_linddCj_fac)

    file.write('For Troe\n')
    dFi_troedCj_unity = __get_fi_dcj(dFi_troedCj, dPri_unitydCj_fac, dFi_troedCj_fac)

    file.write('For SRI\n')
    dFi_sridCj_unity = __get_fi_dcj(dFi_sridCj, dPri_unitydCj_fac, dFi_sridCj_fac)


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
                           r'\usepackage[colorlinks=false]{hyperref}' + '\n'
                           r'\newcommand{\pluseq}{\mathrel{{+}{=}}}' + '\n' +
                           r'\newcommand{\minuseq}{\mathrel{{-}{=}}}' + '\n' +
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

    class equation_file(object):
        def __init__(self, name, mode):
            import re
            self.name = os.path.join(out_dir, name)
            self.mode = mode
            self.equations = {}

        def __enter__(self):
            return self

        def write(self, variable, equation):
            assert variable not in self.equations
            self.equations[variable] = equation

        def write_conditional(self, variable, equation):
            if variable not in self.equations:
                self.equations[variable] = [equation]
            else:
                self.equations[variable].append(equation)

        def __exit__(self, type, value, traceback):
            variables = set()
            for var, eqn in self.equations.items():
                if isinstance(eqn, list):
                    variables = variables.union(set([var]))
                    for e, *conditions in eqn:
                        variables = variables.union(e.free_symbols)
                else:
                    variables = variables.union(set([var]).union(eqn.free_symbols))
            #write equations
            with open(os.path.join(home_dir, self.name), self.mode) as file:
                for var in variables:
                    file.write(srepr(var) + '\n')
                file.write('\n')
                for var, eqn in self.equations.items():
                    file.write(srepr(var) + '\n')
                    if isinstance(eqn, list):
                        for e, *conditions in eqn:
                            file.write('if {}\n{}\n'.format(','.join([srepr(c) for c in conditions]), srepr(eqn)))
                    else:
                        file.write(srepr(eqn) + '\n')



    from argparse import ArgumentParser
    parser = ArgumentParser(description='generates derivations for SPyJac')
    parser.add_argument('-conv', '--constant_volume',
                         action='store_true',
                         default=False)

    args = parser.parse_args()
    conv = args.constant_volume

    with filer('con{}_derivation.tex'.format('v' if conv else 'p'), 'w') as file:
        with equation_file('con{}_derivation.sympy'.format('v' if conv else 'p'), 'w') as efile:
            derivation(file, efile, not conv, True)