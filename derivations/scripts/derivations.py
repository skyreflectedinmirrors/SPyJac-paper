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
from sympy.tensor.indexed import Idx
from sympy.concrete import Sum, Product
from sympy.printing.latex import LatexPrinter
from sympy.printing.repr import ReprPrinter
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
from sympy_addons import ImplicitSymbol, MyIndexedBase
from custom_sympy_classes import MyImplicitSymbol, MyIndexedFunc, IndexedConc
from reaction_types import *
import os

home_dir = os.path.dirname(os.path.realpath(__file__))
out_dir = os.path.realpath(os.path.join(
    home_dir, '..', 'tex'))

sympyfile = None
latexfile = None

init_printing()

# weights taken from http://arxiv.org/pdf/1506.03997.pdf
# note these are rough estimates and hardware dependent
# feel free to change


def count_ops_div(expr, div_weight=34, mul_weight=5, add_weight=3,
                  large_factor=100):
    expr = count_ops(expr, visual=True)
    expr = expr.xreplace({Symbol('DIV'): div_weight,
                          Symbol('MUL'): mul_weight,
                          Symbol('ADD'): add_weight,
                          Symbol('NEG'): mul_weight,
                          Symbol('SUB'): add_weight}
                         )
    # everything else is powers, exp, log, etc, so replace with large factor
    expr = expr.xreplace({x: large_factor for x in expr.free_symbols})
    return expr


class CustomLatexPrinter(LatexPrinter):

    def _print_ExpBase(self, expr, exp=None):
        tex = r"\operatorname{exp}\left({%s}\right)" % self._print(
            expr.args[0])
        return self._do_exponent(tex, exp)

# override default latex print method


def latex(expr, **settings):
    return CustomLatexPrinter(settings).doprint(expr)


class CustomReprPrinter(ReprPrinter):

    def __get_func_form(self, expr):
        return self._print(expr.functional_form)

    def _print_NumberSymbol(self, expr):
        return repr(expr)

    def _print_Float(self, expr):
        return repr(expr)

    def _print_IndexedFunc(self, expr):
        r = expr.__class__.__name__
        r += '(%s,%s)' % (srepr(expr.label), self.__get_func_form(expr))
        return r

    def _print_ImplicitSymbol(self, expr):
        d = expr._assumptions.generator
        if d == {}:
            return "%s(%s, %s)" % (expr.__class__.__name__, self._print(expr.name),
                                   self.__get_func_form(expr))
        else:
            attr = ['%s=%s' % (k, v) for k, v in d.items()]
            return "%s(%s, %s, %s)" % (expr.__class__.__name__,
                                       self.__get_func_form(expr),
                                       self._print(expr.name), ', '.join(attr))


def filter(s):
    return s.replace('\\\\', '\\').replace('\\', '')


def srepr(expr, **settings):
    return filter(CustomReprPrinter(settings).doprint(expr))


def write_eq(*args, **kw_args):
    if len(args) == 2:
        latexfile.write(latex(Eq(args[0], args[1]), mode='equation') + '\n')
    else:
        latexfile.write(latex(*args, mode='equation') + '\n')
    if 'sympy' in kw_args and kw_args.pop('sympy'):
        assert len(args) == 2
        if 'enum_conds' in kw_args:
            enums = kw_args.pop('enum_conds')
            if len(args) != 2:
                assert "I don't know how to register this!"
            sympyfile.write_conditional(args[0], (args[1], enums))
        else:
            sympyfile.write(args[0], args[1])
    if 'register' in kw_args and kw_args.pop('register'):
        if len(args) != 2:
            assert "I don't know how to register this!"
        register_equal(args[0], args[1])
    if 'enum_conds' in kw_args:
        enums = kw_args.pop('enum_conds')
        if len(args) != 2:
            assert "I don't know how to register this!"
        sympyfile.write_conditional(args[0], (args[1], enums))
    if len(kw_args):
        raise Exception('Unknown kw_args: {}'.format(str(kw_args)))


def write_dummy_eq(text, **kw_args):
    latexfile.write(r'\begin{equation}' + text + r'\end{equation}' + '\n')


def write_conditional(arg1, arg2, text=None, enum_conds=None, register=False):
    if text is not None:
        outtext = r'\begin{equation}' + latex(arg1) + '=' + latex(arg2) +\
            r'\text{{{}}}'.format(text) + r'\end{equation}'
    else:
        outtext = latex(Eq(arg1, arg2), mode='equation')
    latexfile.write(outtext + '\n')
    if enum_conds is not None:
        sympyfile.write_conditional(arg1, (arg2, enum_conds))
    if register:
        assert enum_conds is None
        register_equal(arg1, arg2)


def write_section(title, **kw_args):
    sec_type = ''
    if 'sub' in kw_args and kw_args['sub']:
        sec_type = 'sub'
    elif 'subsub' in kw_args and kw_args['subsub']:
        sec_type = 'subsub'
    latexfile.write(r'\{0}section{{{1}}}'.format(sec_type, title) + '\n')


def write_cases(variable, case_list, **kw_args):
    latexfile.write(r'\begin{dgroup}' + '\n')

    for case_var, case_text in case_list:
        latexfile.write(r'\begin{{dmath}} {} = {}\text{{\quad if {}}}\end{{dmath}}'.format(
            latex(variable), latex(case_var), case_text) + '\n')
    latexfile.write(r'\end{dgroup}' + '\n')


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
                        # test that we can actually compare the limits
                        try:
                            # and that the second >= first
                            if limit[1] >= limit[2]:
                                # no sum/product
                                continue
                        except:
                            pass
                        # valid limit
                        limit_list = limit_list + (limit,)
                    if not limit_list:
                        # no remaining valid limits
                        out_terms.append(
                            term.function.subs(term.limits[0][0], term.limits[0][1]))
                    else:
                        out_terms.append(
                            term.__class__(term.function, *limit_list))
                else:
                    out_terms.append(term)
            return Mul(*out_terms)
        # weed out dummy sums
        v1 = __rep_dummy_sum(v1)
        v2 = __rep_dummy_sum(v2)

        if v1 == v2:
            return True

        # special cases
        # kronecker delta collapses
        if v1.has(KroneckerDelta) and (
                isinstance(v1, Sum) or (isinstance(v1, Mul) and v1.has(Sum))):
            if isinstance(v1, Mul) and v1.has(Sum):
                # refactor to get the Sum form
                sumv = next(
                    (x for x in Mul.make_args(v1) if isinstance(x, Sum)),
                    None)
                if sumv is not None:
                    sumv = Sum(Mul(
                        *([sumv.function] +
                          [x for x in Mul.make_args(v1) if x != sumv])),
                        sumv.limits)
            else:
                sumv = v1
            if sumv is not None:
                # get the KD term
                func = sumv.function
                args = Mul.make_args(factor_terms(func))
                KD = next(
                    (x for x in args if isinstance(x, KroneckerDelta)), None)
                # check that the substitution is formatted as we thought
                assert KD is not None
                # and that the KD includes the summation variable
                sum_var = next(v for v in KD.args if v == sumv.limits[0][0])
                other_var = next(v for v in KD.args if v != sum_var)
                # and finally, return test equal
                # on the collapsed sum
                return test_equal(Mul(*[
                    x.subs(sum_var, other_var) for x in args if x != KD]), v2)
        # sum of vals to Ns -> sum vals to Ns - 1 + val_ns
        # OR
        # sum vals to Ns -> val_k * sum of vals 1 to k - 1, k + 1 to Ns
        # OR
        # product of vals to Ns -> product vals to Ns - 1 * val_ns
        # OR
        # product vals to Ns -> val_k * product of vals 1 to k - 1, k + 1 to Ns
        # OR
        # the reverse

        def __sum_test(v1, v2):
            if v1 in equivalences:
                if any(v1t == v2 for v1t in equivalences[v1]):
                    return True
            elif -v1 in equivalences:
                if any(v1t == -v2 for v1t in equivalences[-v1]):
                    return True
            if v2 in equivalences:
                if any(v2t == v1 for v2t in equivalences[v2]):
                    return True
            elif -v2 in equivalences:
                if any(v2t == -v1 for v2t in equivalences[-v2]):
                    return True
            lim = v1.limits[0]
            # get the Ns term, and test equivalence
            v2Ns = next((x for x in v2.args if
                         test_equal(v1.function.subs(lim[0], lim[2]), x)),
                        None)

            if v2Ns is None:
                # try to find a mid term
                v2sum = next((
                    x for x in v2.args if
                    (isinstance(x, Sum) or isinstance(x, Product)) and
                    test_equal(
                        v1.function, x.function)
                ), None)

                # test that the limits look right
                retv = v2sum is not None

                # test that it has right number of limits
                retv = retv and len(v2sum.limits) == 2

                # check that the same variable
                retv = retv and v2sum.limits[0][0] == v2sum.limits[1][0]

                # check that the limits are next to each other
                retv = retv and v2sum.limits[1][1] - v2sum.limits[0][2] == 2

                # check start and end of limits
                retv = retv and v2sum.limits[0][1] == v1.limits[0][1]
                retv = retv and v2sum.limits[1][2] == v1.limits[0][2]

                if retv:
                    # and find the mid value
                    middy = (v2sum.limits[1][1] + v2sum.limits[0][2]) / 2

                    # and check that the other value is correct
                    # find the non sum term in v2
                    v2k = next((arg for arg in v2.args if arg != v2sum),
                               None)
                    retv = retv and test_equal(v1.function.subs(
                        v1.limits[0][0],
                        middy), v2k)
            else:
                retv = v2Ns is not None

                # get the sum term in v2
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

        def __test_product_rule(v1, v2):
            # tests product rule for derivative of sympy Product's
            # v1 -> derivative(Product)
            # v2 -> sum of product derivatives

            # test that v1 is derivative of product
            retv = isinstance(v1, Derivative) and v1.args[0].has(Product)
            # and that v2 is of form Sum(Aval * product(...))
            retv = retv and isinstance(v2, Sum)
            retv = retv and len([x for x in Mul.make_args(v2.function)
                                 if isinstance(x, Product)]) == 1
            if not retv:
                return False

            try:
                Aval_given = Mul(*[x for x in Mul.make_args(v2.function)
                                   if not isinstance(x, Product)])

                mod_prod = next((x for x in Mul.make_args(v2.function)
                                 if isinstance(x, Product)), None)
            except:
                return False

            retv = retv and Aval_given is not None and mod_prod is not None
            if not retv:
                return False

            # find product
            prod, diff_by = v1.args
            # next make sure the v2 sum has same limits
            retv = retv and prod.limits[0][1] == v2.limits[0][1] and \
                prod.limits[0][2] == v2.limits[0][2]

            # v2 should then have be the sum of Aval * mod_prod with
            # Aval == derivative of prod.function, and mod_prod the product
            # with Aval removed

            # test Aval
            Aval = prod.function.subs(prod.limits[0][0], v2.limits[0][0])
            retv = retv and test_equal(diff(Aval, diff_by), Aval_given)

            # test mod_prod value
            retv = retv and prod.function.subs(
                prod.limits[0][0], mod_prod.limits[0][0]) == mod_prod.function

            # and mod_prod limits
            retv = retv and mod_prod.limits[0][2] == v2.limits[0][0] - 1
            retv = retv and mod_prod.limits[1][1] == v2.limits[0][0] + 1

            return retv

        if isinstance(v1, Derivative) and v1.has(Product) \
                and isinstance(v2, Sum) and v2.has(Product):
            if __test_product_rule(v1, v2):
                return True
        if isinstance(v2, Derivative) and v2.has(Product) \
                and isinstance(v1, Sum) and v1.has(Product):
            if __test_product_rule(v2, v1):
                return True

        # test switch of sum variable
        if (((isinstance(v1, Sum) and isinstance(v2, Sum)) or
             (isinstance(v1, Product) and isinstance(v2, Product))) and
                v2.function.subs(v2.limits[0][0], v1.limits[0][0]) == v1.function and
                v2.limits[0][1:] == v1.limits[0][1:]):
            return True

        if v1 in equivalences:
            if any(v1t == v2 for v1t in equivalences[v1]):
                return True
        elif -v1 in equivalences:
            if any(v1t == -v2 for v1t in equivalences[-v1]):
                return True
        if v2 in equivalences:
            if any(v2t == v1 for v2t in equivalences[v2]):
                return True
        elif -v2 in equivalences:
            if any(v2t == -v1 for v2t in equivalences[-v2]):
                return True

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

assumptions = {}

"""{'float' : True,
               'finite' : True,
               'negative' : False,
               'postive' : True,
               'real' : True}
"""


def __simplify_per_term(term, separator=Add):
    return separator(*[simplify(x) for x in separator.make_args(term)])


def __separate_on(term, separate_on, separator_class=Add):
    withterms = []
    withoutterms = []
    try:
        for x in separator_class.make_args(term):
            if any(x.has(sep) for sep in separate_on):
                withterms.append(x)
            else:
                withoutterms.append(x)
    except:
        for x in separator_class.make_args(term):
            if x.has(separate_on):
                withterms.append(x)
            else:
                withoutterms.append(x)
    return separator_class(*withterms), separator_class(*withoutterms)


def __complex_collect(obj, term_list, expand=False):
    if not isinstance(term_list, list):
        term_list = [term_list]
    temp_syms = [Symbol('temp{}'.format(i)) for i in range(len(term_list))]
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


def _derivation(file, efile, conp=True, thermo_deriv=False):
    # set files
    global latexfile
    latexfile = file
    global sympyfile
    sympyfile = efile

    # time
    t = symbols('t', **assumptions)

    # thermo vars
    T = MyImplicitSymbol('T', t, **assumptions)

    # specific heats, etc.
    cp = MyIndexedFunc(r'{C_p}', T)
    cv = MyIndexedFunc(r'{C_v}', T)
    h = MyIndexedFunc(r'H', T)
    u = MyIndexedFunc(r'U', T)

    # mechanism size
    Ns = S.Ns
    Nr = S.Nr

    # index variables
    k = Idx('k')
    i = Idx('i')
    j = Idx('j')
    l = Idx('l')
    m = Idx('m')

    # molecular weight
    Wk = MyIndexedBase('W')

    # some constants, and state variables
    Patm = S.atm_pressure
    R = S.gas_constant
    m_sym = S.mass

    # polyfits
    a = MyIndexedBase('a')

    write_section('State Variables')
    # thermo vars
    nk = IndexedConc('n', t)

    # define concentration
    if conp:
        P = S.pressure
        V = MyImplicitSymbol('V', t, **assumptions)
        state_vec = [T, V, nk[1], nk[2], nk[Ns - 1]]
        extra_var_name = 'Volume'
    else:
        P = MyImplicitSymbol('P', t, **assumptions)
        V = S.volume
        state_vec = [T, P, nk[1], nk[2], nk[Ns - 1]]
        extra_var_name = 'Pressure'
    extra_var = state_vec[1]

    Ck = MyIndexedFunc('[C]', (nk, V))

    write_eq(Ck[k], nk[k] / V, register=True),

    # rates
    wdot = MyIndexedFunc(Symbol(r'\dot{\omega}'), args=(nk, T, P, V))

    # define state vector
    state_vec_str = ' = ' + r'\left\{{{}\ldots {}\right\}}'
    state = MyImplicitSymbol(r'\Phi', t)
    write_dummy_eq(str(state) + state_vec_str.format(
        ','.join([str(x) for x in state_vec[:-1]]),
        str(state_vec[-1])))

    write_dummy_eq(str(diff(state, t)) + state_vec_str.format(
        ','.join([str(diff(x, t)) for x in state_vec[:-1]]),
        str(diff(state_vec[-1], t))))

    # write equations
    write_section('Source Terms')
    dnkdt_sym = diff(nk[k], t)
    dnkdt = wdot[k] * V
    write_eq(dnkdt_sym, dnkdt, register=True)

    register_equal(dnkdt_sym / V, dnkdt / V)

    dTdt_sym = diff(T, t)
    if conp:
        energy = h
        dTdt = -Sum(h[k] * wdot[k], (k, 1, Ns)) / \
            Sum(Ck[k] * cp[k], (k, 1, Ns))
    else:
        energy = u
        dTdt = -Sum(u[k] * wdot[k], (k, 1, Ns)) / \
            Sum(Ck[k] * cv[k], (k, 1, Ns))
    write_eq(dTdt_sym, dTdt, register=True, sympy=True)

    latexfile.write('From conservation of mass:\n')
    n_eq = Sum(nk[k] * Wk[k], (k, 1, Ns))
    write_eq(m_sym, n_eq)
    dmdt = Sum(Wk[k] * diff(nk[k], t), (k, 1, Ns))
    write_eq(diff(m_sym, t), dmdt)

    dnNsdt = assert_subs(
        dmdt,
        (Sum(Wk[k] * diff(nk[k], t), (k, 1, Ns)),
         Sum(Wk[k] * diff(nk[k], t), (k, 1, Ns - 1))
         + Wk[Ns] * diff(nk[Ns], t)))

    dnNsdt = solve(
        Eq(diff(m_sym, t), dnNsdt), diff(nk[Ns], t))[0]

    # get rid of KD for k and Ns
    dnNsdt = assert_subs(
        dnNsdt,
        (Sum(KroneckerDelta(Ns, k) * Wk[k], (k, 1, Ns - 1)), S.Zero),
        assumptions=[(
            Sum(KroneckerDelta(Ns, k) * Wk[k], (k, 1, Ns - 1)), S.Zero)])

    write_eq(diff(nk[Ns], t), dnNsdt, register=True)

    n_sym = MyImplicitSymbol('n', args=(t,), **assumptions)
    write_eq(n_sym, P * V / (R * T), register=True)
    dndt = assert_subs(Sum(diff(nk[k], t), (k, 1, Ns)), (
        diff(nk[k], t), dnkdt_sym))
    dndt_sym = diff(n_sym, t)

    latexfile.write('Thus...')
    wdot_ns = assert_subs(diff(nk[Ns], t),
                          (diff(nk[Ns], t), wdot[Ns] * V),
                          assumptions=[(Ns, k)])
    dwdotNsdt = assert_subs(dnNsdt,
                            (diff(nk[k], t), wdot[k] * V))
    dwdotNsdt = solve(
        Eq(wdot_ns, dwdotNsdt), wdot[Ns])[0]
    dwdotNsdt = assert_subs(
        dwdotNsdt,
        (Sum(KroneckerDelta(Ns, k) * Wk[k], (k, 1, Ns - 1)), S.Zero),
        assumptions=[
            (Sum(KroneckerDelta(Ns, k) * Wk[k], (k, 1, Ns - 1)), S.Zero)])
    write_eq(wdot[Ns], dwdotNsdt, register=True)

    latexfile.write('And...')
    dTdt = assert_subs(
        dTdt,
        (Sum(energy[k] * wdot[k], (k, 1, Ns)),
         Sum(energy[k] * wdot[k], (k, 1, Ns - 1)) +
         energy[Ns] * dwdotNsdt)
    )
    dTdt = __simplify_per_term(dTdt, Mul)
    write_eq(dTdt_sym, dTdt)

    write_eq(dndt_sym, dndt)

    dndt = simplify(assert_subs(dndt, (
        Sum(diff(nk[k], t), (k, 1, Ns)),
        Sum(diff(nk[k], t), (k, 1, Ns - 1)) + diff(nk[Ns], t),
    ), (
        diff(nk[Ns], t), dnNsdt)))

    write_eq(dndt_sym, dndt, register=True)

    latexfile.write('From the ideal gas law:\n')

    ideal_gas = Eq(P * V, n_sym * R * T)

    extra_var_eq = solve(ideal_gas, extra_var)[0]
    dExdt_sym = diff(extra_var, t)
    dExdt = simplify(diff(extra_var_eq, t))

    write_eq(dExdt_sym, dExdt)

    # sub in dT/dt and dn/dt

    dExdt = simplify(assert_subs(dExdt, (
        diff(n_sym, t), dndt), (
        diff(nk[k], t), dnkdt), (
        n_sym, P * V / (R * T))
    ))

    write_eq(dExdt_sym, dExdt)

    write_section('Other defns', sub=True)

    Ctot_sym = MyImplicitSymbol('[C]', args=(T, P), **assumptions)
    Ctot = P / (R * T)
    write_eq(Ctot_sym, Ctot, sympy=True)
    register_equal([(Ctot_sym, Ctot), (Ctot_sym, n_sym / V),
                    (Ctot_sym, Sum(Ck[k], (k, 1, Ns)))])

    dExdt = simplify(assert_subs(dExdt, (
        1 / Ctot, 1 / Ctot_sym),
        assumptions=[(1 / Ctot, 1 / Ctot_sym)]
    ))
    write_eq(dExdt_sym, dExdt, register=True, sympy=True)

    Cns = Ctot_sym - Sum(Ck[k], (k, 1, Ns - 1))
    write_eq(Ck[Ns], Cns, sympy=True, register=True)
    Cns = assert_subs(Cns, (Ctot_sym, Ctot))
    write_eq(Ck[Ns], Cns, register=True)
    register_equal(Ck[Ns], assert_subs(Cns, (Ctot, Ctot_sym)))

    # mole fractions
    Xk = MyIndexedBase('X')
    register_equal(Xk[k], Ck[k] / Ctot_sym)

    # molecular weight
    W_sym = MyImplicitSymbol('W', t)
    W = Sum(Wk[k] * Xk[k], (k, 1, Ns))
    write_eq(W_sym, W)
    W = simplify(assert_subs(W, (Xk[k], Ck[k] / Ctot_sym)))
    write_eq(W_sym, W, sympy=True)
    Cns_sym = assert_subs(Cns, (Ctot, Ctot_sym))
    write_eq(Ck[Ns], Cns, register=True)

    W = assert_subs(W, (Sum(Wk[k] * Ck[k], (k, 1, Ns)),
                        Sum(Wk[k] * Ck[k], (k, 1, Ns - 1)) + Wk[Ns] * Cns_sym))
    write_eq(W_sym, W)
    W = simplify(W)
    write_eq(W_sym, W)

    write_section('Thermo Definitions')

    # thermo derivation
    cpfunc = R * \
        (a[k, 0] + T * (a[k, 1] + T * (a[k, 2] + T * (a[k, 3] + a[k, 4] * T))))

    cp_tot_sym = MyImplicitSymbol(r'\bar{c_p}', T)

    cp_tot = Sum(nk[k] / n_sym * cp[k], (k, 1, Ns))
    write_eq(Symbol(r'{C_{p,k}}^{\circ}'), cp[k])
    write_eq(cp[k], cpfunc, sympy=True)
    write_eq(cp[k], expand(cpfunc))
    write_eq(diff(cp[k], T), simplify(diff(cpfunc, T)))
    dcpdT = R * \
        (a[k, 1] + T * (2 * a[k, 2] + T * (3 * a[k, 3] + 4 * a[k, 4] * T)))
    dcpdT = assert_subs(diff(cpfunc, T), (
        diff(cpfunc, T), dcpdT
    ))
    write_eq(diff(cp[k], T), dcpdT, sympy=True)
    write_eq(cp_tot_sym, cp_tot)

    cvfunc = simplify(cpfunc - R)
    cv = MyIndexedFunc(r'{C_v}', T)
    cv_tot_sym = MyImplicitSymbol(r'\bar{c_v}', T)
    cv_tot = Sum(nk[k] / n_sym * cv[k], (k, 1, Ns))
    write_eq(Symbol(r'{C_{v,k}}^{\circ}'), cv[k])
    write_eq(cv[k], cvfunc, sympy=True)
    write_eq(cv[k], expand(cvfunc))
    write_eq(diff(cv[k], T), simplify(diff(cvfunc, T)))
    dcvdT = assert_subs(diff(cvfunc, T), (
        diff(cvfunc, T), R * (a[k, 1] + T * (
            2 * a[k, 2] + T * (3 * a[k, 3] + T * 4 * a[k, 4])))
    ))
    write_eq(diff(cv[k], T), dcvdT, sympy=True)
    write_eq(cv_tot_sym, cv_tot)

    hfunc = R * (T * (a[k, 0] + T * (a[k, 1] * Rational(1, 2) + T * (
        a[k, 2] * Rational(1, 3) + T * (
            a[k, 3] * Rational(1, 4) + a[k, 4] * T * Rational(1, 5))
    ))) + a[k, 5])

    # check that the dH/dT = cp identity holds
    write_eq(Symbol(r'H_k^{\circ}'), h[k])
    write_eq(h[k], hfunc, sympy=True, register=True)
    write_eq(h[k], expand(hfunc))
    dhdT = simplify(diff(hfunc, T))
    dhdT = assert_subs(dhdT, (
        dhdT, R * (a[k, 0] + T * (a[k, 1] + T * (
            a[k, 2] + T * (a[k, 3] + T * a[k, 4]))))))
    write_eq(diff(h[k], T), dhdT, sympy=True)

    # and du/dT
    write_dummy_eq(r'H_k = U_k + \frac{P V}{n}')
    write_eq(u[k], h[k] - R * T)
    ufunc = h[k] - R * T
    ufunc = collect(assert_subs(ufunc, (h[k], hfunc)), R)
    write_eq(u[k], ufunc, sympy=True)
    dudT = diff(ufunc, T)
    dudT = assert_subs(dudT, (
        dudT, R * (-1 + a[k, 0] + T * (a[k, 1] + T * (
            a[k, 2] + T * (a[k, 3] + T * a[k, 4]))))))
    write_eq(diff(u[k], T), dudT, sympy=True)

    # finally do the entropy and B terms
    Sfunc = R * (a[k, 0] * log(T) + T * (a[k, 1] + T * (a[k, 2] * Rational(1, 2) +
                                                        T * (a[k, 3] * Rational(1, 3) + a[k, 4] * T * Rational(1, 4)))) + a[k, 6])
    s = MyIndexedFunc(r'S', T)
    write_eq(Eq(Symbol(r'S_k^{\circ}'), s[k]), Sfunc)

    Jac = MyIndexedBase(r'\mathcal{J}', (Ns - 1, Ns - 1))

    # reaction rates
    write_section('Definitions')
    nu_f = MyIndexedBase(r'\nu^{\prime}')
    nu_r = MyIndexedBase(r'\nu^{\prime\prime}')
    nu = nu_f[k, i] - nu_r[k, i]
    nu_sym = MyIndexedBase(r'\nu')
    write_eq(nu_sym[k, i], nu)

    q_sym = MyIndexedFunc('q', args=(nk, T, V, P))
    omega_k = Sum(nu_sym[k, i] * q_sym[i], (i, 1, Nr))
    omega_sym_q_k = omega_k
    write_eq(wdot[k], omega_k, register=True)

    Rop_sym = MyIndexedFunc('R', args=(nk, T, V, P))
    ci = MyIndexedFunc('c', args=(nk, T, V, P))
    q = Rop_sym[i] * ci[i]

    write_eq(q_sym[i], q, register=True)
    omega_k = assert_subs(omega_k, (q_sym[i], q))
    write_eq(wdot[k], omega_k, sympy=True)

    # arrhenius coeffs
    A = MyIndexedBase(r'A')
    Beta = MyIndexedBase(r'\beta')
    Ea = MyIndexedBase(r'{E_{a}}')

    write_section('Rate of Progress')
    Ropf_sym = MyIndexedFunc(r'{R_f}', args=(nk, T, V, P))
    Ropr_sym = MyIndexedFunc(r'{R_r}', args=(nk, T, V, P))

    Rop = Ropf_sym[i] - Ropr_sym[i]
    write_eq(Rop_sym[i], Ropf_sym[i] - Ropr_sym[i], sympy=True, register=True)

    kf_sym = MyIndexedFunc(r'{k_f}', T)
    Ropf = kf_sym[i] * Product(Ck[k]**nu_f[k, i], (k, 1, Ns))
    write_eq(Ropf_sym[i], Ropf, sympy=True, register=True)

    kr_sym = MyIndexedFunc(r'{k_r}', T)
    Ropr = kr_sym[i] * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write_eq(Ropr_sym[i], Ropr, register=True)

    write_section('Third-body effect')
    # write the various ci forms
    ci_elem = Integer(1)
    write_conditional(
        ci[i], ci_elem, r'\quad for elementary reactions', enum_conds=reaction_type.elementary)

    ci_thd_sym = MyImplicitSymbol('[X]_i', args=(nk, T, V, P))
    write_conditional(
        ci[i], ci_thd_sym, r'\quad for third-body enhanced reactions', enum_conds=reaction_type.thd)

    Pri_sym = MyImplicitSymbol('P_{r, i}', args=(nk, T, V, P))
    Fi_sym = MyImplicitSymbol('F_{i}', args=(nk, T, V, P))
    ci_fall = (Pri_sym / (1 + Pri_sym)) * Fi_sym
    write_conditional(ci[i], ci_fall, r'\quad for unimolecular/recombination falloff reactions',
                      enum_conds=[reaction_type.fall])

    ci_chem = (1 / (1 + Pri_sym)) * Fi_sym
    write_conditional(ci[i], ci_chem, r'\quad for chemically-activated bimolecular reactions',
                      enum_conds=[reaction_type.chem])

    write_section('Forward Reaction Rate')
    kf = A[i] * (T**Beta[i]) * exp(-Ea[i] / (R * T))
    write_eq(kf_sym[i], kf, register=True,
             enum_conds=[reaction_type.elementary, reaction_type.thd, reaction_type.fall, reaction_type.chem])

    write_section('Equilibrium Constants')
    Kp_sym = MyIndexedFunc(r'{K_p}', args=(T, a))
    Kc_sym = MyIndexedFunc(r'{K_c}', args=(T))
    write_eq(
        Kc_sym[i], Kp_sym[i] * ((Patm / (R * T))**Sum(nu_sym[k, i], (k, 1, Ns))))

    write_dummy_eq(latex(Kp_sym[i]) + ' = ' +
                   r'\text{exp}(\frac{\Delta S^{\circ}_k}{R_u} - \frac{\Delta H^{\circ}_k}{R_u T})')
    write_dummy_eq(latex(Kp_sym[i]) + ' = ' +
                   r'\text{exp}(\sum_{k=1}^{N_s}\frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T})')

    B_sym = MyIndexedFunc('B', T)
    Kc = ((Patm / R)**Sum(nu_sym[k, i], (k, 1, Ns))) * \
        exp(Sum(nu_sym[k, i] * B_sym[k], (k, 1, Ns)))
    write_eq(Kc_sym[i], Kc, sympy=True, register=True)

    write_dummy_eq(latex(
        B_sym[k]) + r'= \frac{S^{\circ}_k}{R_u} - \frac{H^{\circ}_k}{R_u T} - ln(T)')

    Bk = simplify(Sfunc / R - hfunc / (R * T) - log(T))
    Bk_rep = a[k, 6] - a[k, 0] + (a[k, 0] - Integer(1))*log(T) +\
        T * (a[k, 1] * Rational(1, 2) + T * (a[k, 2] * Rational(1, 6) + T *
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

    A_rexp = MyIndexedBase(r'{A_{r}}')
    Beta_rexp = MyIndexedBase(r'{\beta_r}')
    Ea_rexp = MyIndexedBase(r'{E_{a,r}}')
    kr_rexp = A_rexp[i] * T**Beta_rexp[i] * exp(-Ea_rexp[i] / (R * T))
    Ropr_rexp = kr_rexp * Product(Ck[k]**nu_r[k, i], (k, 1, Ns))
    write_conditional(Ropr_sym[i], Ropr_rexp, r'\quad if explicit',
                      enum_conds=reversible_type.explicit)

    write_section('Third-Body Efficiencies')
    thd_bdy_eff = MyIndexedBase(r'\alpha')
    ci_thd = Sum(thd_bdy_eff[k, i] * Ck[k], (k, 1, Ns))
    write_eq(ci_thd_sym, ci_thd)

    ci_thd = assert_subs(
        ci_thd,
        (Sum(thd_bdy_eff[k, i] * Ck[k], (k, 1, Ns)),
         Sum((thd_bdy_eff[k, i] - 1) * Ck[k], (k, 1, Ns)) +
            Sum(Ck[k], (k, 1, Ns))),
        (Sum(Ck[k], (k, 1, Ns)),
         Ctot_sym),
    )

    write_eq(ci_thd_sym, ci_thd)

    ci_thd = assert_subs(ci_thd,
                         (Sum((thd_bdy_eff[k, i] - 1) * Ck[k], (k, 1, Ns)),
                          Sum((thd_bdy_eff[k, i] - 1) * Ck[k], (k, 1, Ns - 1)) + (thd_bdy_eff[Ns, i] - 1) * Ck[Ns]),
                         (Ck[Ns], Cns))
    write_eq(ci_thd_sym, ci_thd)
    ci_thd = assert_subs(ci_thd, (Ctot, Ctot_sym))
    ci_thd = simplify(ci_thd)
    write_conditional(ci_thd_sym, ci_thd, text=r'\quad for mixture as third-body',
                      enum_conds=thd_body_type.mix)

    ci_thd_unity = assert_subs(ci_thd, (thd_bdy_eff[k, i], S.One),
                               (thd_bdy_eff[Ns, i], S.One),
                               assumptions=[(thd_bdy_eff[k, i], S.One),
                                            (thd_bdy_eff[Ns, i], S.One)])
    ci_thd_unity = simplify(ci_thd_unity)
    write_conditional(ci_thd_sym, ci_thd_unity, text=r'\quad for all $\alpha_{ki} = 1$',
                      enum_conds=thd_body_type.unity)

    ci_thd_species = KroneckerDelta(Ns, m) * Cns + (
        1 - KroneckerDelta(Ns, m)) * Ck[m]

    ci_thd_species = assert_subs(ci_thd_species, (
        Ctot, Ctot_sym))
    write_conditional(ci_thd_sym, ci_thd_species, text=r'\quad for a single species third-body',
                      enum_conds=thd_body_type.species)

    write_section('Falloff Reactions')
    k0 = Symbol('A_0') * T**Symbol(r'\beta_0') * \
        exp(-Symbol('E_{a, 0}') / (R * T))
    kinf = Symbol(r'A_{\infty}') * T**Symbol(r'\beta_{\infty}') * \
        exp(-Symbol(r'E_{a, \infty}') / (R * T))
    k0_sym = MyImplicitSymbol(r'k_{0, i}', T)
    write_eq(k0_sym, k0, sympy=True, register=True)
    kinf_sym = MyImplicitSymbol(r'k_{\infty, i}', T)
    write_eq(kinf_sym, kinf, sympy=True, register=True)

    Pri_mix = ci_thd_sym * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_mix, text=r'\quad for the mixture as the third-body',
                      enum_conds=[thd_body_type.mix])

    Pri_spec = ci_thd_species * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_spec, text=r'\quad for species $m$ as the third-body',
                      enum_conds=[thd_body_type.species])

    Pri_unity = ci_thd_unity * k0_sym / kinf_sym
    write_conditional(Pri_sym, Pri_unity, text=r'\quad for for all $\alpha_{i, j} = 1$',
                      enum_conds=[thd_body_type.unity])

    Fi_lind = Integer(1)
    write_conditional(Fi_sym, Fi_lind, text=r'\quad for Lindemann',
                      enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.lind])

    Fcent_sym = MyImplicitSymbol('F_{cent}', T)
    Atroe_sym = MyImplicitSymbol('A_{Troe}', args=(Pri_sym, Fcent_sym))
    Btroe_sym = MyImplicitSymbol('B_{Troe}', args=(Pri_sym, Fcent_sym))
    Fcent_power = (1 + (Atroe_sym / Btroe_sym)**2)**-1
    Fi_troe = Fcent_sym**Fcent_power
    Fi_troe_sym = ImplicitSymbol('F_{i}', args=(Fcent_sym, Pri_sym))
    register_equal(Fi_troe_sym, Fi_troe)
    write_conditional(Fi_sym, Fi_troe, text=r'\quad for Troe',
                      enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.troe])

    X_sym = MyImplicitSymbol('X', Pri_sym)
    a_fall, b_fall, c_fall, d_fall, e_fall, \
        Tstar, Tstarstar, Tstarstarstar = symbols(
            'a b c d e T^{*} T^{**} T^{***}')
    Fi_sri = d_fall * T ** e_fall * (
        a_fall * exp(-b_fall / T) + exp(-T / c_fall))**X_sym
    write_conditional(Fi_sym, Fi_sri, text=r'\quad for SRI',
                      enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.sri])

    Fcent = (S.One - a_fall) * exp(-T / Tstarstarstar) + a_fall * exp(-T / Tstar) + \
        exp(-Tstarstar / T)
    write_eq(Fcent_sym, Fcent, register=True, sympy=True)

    Atroe = log(Pri_sym, 10) - Float(0.67) * log(Fcent_sym, 10) - Float(0.4)
    write_eq(Atroe_sym, Atroe, register=True, sympy=True)

    Btroe = Float(0.806) - Float(1.1762) * log(Fcent_sym, 10) - \
        Float(0.14) * log(Pri_sym, 10)
    write_eq(Btroe_sym, Btroe, register=True, sympy=True)

    X = (1 + (log(Pri_sym, 10))**2)**-1
    write_eq(X_sym, X, register=True, sympy=True)

    write_section('Pressure-Dependent Reactions')

    # pdep
    latexfile.write('For PLog reactions\n')
    A_1, A_2, beta_1, beta_2, Ea_1, Ea_2 = symbols(r'A_1 A_2 \beta_1' +
                                                   r' \beta_2 E_{a_1} E_{a_2}')
    k1 = A_1 * T**beta_1 * exp(Ea_1 / (R * T))
    k2 = A_2 * T**beta_2 * exp(Ea_2 / (R * T))
    k1_sym = MyImplicitSymbol('k_1', T)
    k2_sym = MyImplicitSymbol('k_2', T)
    write_conditional(k1_sym, k1, text=r'\quad at $P_1$')
    write_conditional(k2_sym, k2, text=r'\quad at $P_2$')

    kf_pdep = log(k1_sym) + (log(k2_sym) - log(k1_sym)) * (log(P) -
                                                           log(Symbol('P_1'))) / (log(Symbol('P_2')) - log(Symbol('P_1')))
    kf_pdep_sym = MyIndexedFunc('{k_f}', (T, P))
    kr_pdep_sym = MyIndexedFunc('{k_r}', (T, P))
    register_equal(log(kf_pdep_sym[i]), kf_pdep)
    write_eq(log(kf_sym[i]), kf_pdep, sympy=True,
             enum_conds=reaction_type.plog)

    # cheb
    latexfile.write('For Chebyshev reactions\n')
    Tmin, Tmax, Pmin, Pmax = symbols('T_{min} T_{max} P_{min} P_{max}')
    Tred = (2 * T**-1 - Tmin**-1 - Tmax**-1) / (Tmax**-1 - Tmin**-1)
    Pred = simplify(
        (2 * log(P, 10) - log(Pmin, 10) - log(Pmax, 10)) / (log(Pmax, 10) - log(Pmin, 10)))
    Tred_sym = MyImplicitSymbol(r'\tilde{T}', T)
    register_equal(diff(Tred_sym, T), diff(Tred, T))
    Pred_sym = MyImplicitSymbol(r'\tilde{P}', P)
    if not conp:
        register_equal(diff(Pred_sym, T), diff(Pred, T))
        register_equal(diff(Pred_sym, extra_var), diff(Pred, extra_var))

    Nt, Np = symbols('N_T N_P')
    eta = MyIndexedBase(r'\eta')
    kf_cheb = Sum(eta[l, j] * chebyshevt(j - 1, Tred_sym) * chebyshevt(l - 1, Pred_sym),
                  (l, 1, Np), (j, 1, Nt))
    kf_cheb_sym = MyIndexedFunc('{k_f}', (T, P))
    kr_cheb_sym = MyIndexedFunc('{k_r}', (T, P))
    register_equal(log(kf_cheb_sym[i], 10), kf_cheb)
    write_eq(log(kf_sym[i], 10), kf_cheb, sympy=True,
             enum_conds=reaction_type.cheb)
    write_eq(Tred_sym, Tred, register=True, sympy=True)
    write_eq(Pred_sym, Pred, register=True, sympy=True)

    write_section('Derivatives')
    write_eq(diff(q_sym[i], T), diff(q, T))
    write_eq(diff(wdot[k], T), diff(omega_k, T), sympy=True)

    write_eq(diff(q_sym[i], nk[k]), diff(q, nk[j]))
    write_eq(diff(wdot[k], nk[j]), diff(omega_k, nk[j]), sympy=True)

    write_eq(diff(q_sym[i], extra_var), diff(q, extra_var))
    write_eq(diff(wdot[k], extra_var), diff(omega_k, extra_var), sympy=True)

    write_section('Rate of Progress Derivatives')

    write_section('Molar Derivatives', sub=True)
    write_eq(diff(Ropf_sym, nk[k]), diff(Ropf, nk[j]))

    Cns_working = assert_subs(Cns, (Ck[k], nk[k] / V))
    register_equal(Cns_working, Ck[Ns])

    dCkdnj = diff(assert_subs(
        Ck[k], (Ck[k], nk[k] / V)), nk[j])
    write_dummy_eq(r'\frac{\partial [C_k]}{\partial n_j} =' + latex(
        dCkdnj))

    dCnsnj_orig = simplify(diff(Cns_working, nk[j]))
    dCnsdnj = assert_subs(
        dCnsnj_orig, (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), S.One))

    write_dummy_eq(
        r'\frac{\partial [C_{Ns}]}{\partial n_j} =' + latex(dCnsdnj))

    dCnsdnj_pow = diff(Cns_working**nu_f[Ns, i], nk[j])
    write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial [n_j]} =' + latex(
        dCnsdnj_pow))

    dCnsdnj_pow = simplify(assert_subs(dCnsdnj_pow, (Cns_working, Ck[Ns])))
    dCnsdnj_pow = assert_subs(dCnsdnj_pow,
                              (Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1))
    write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial n_j} =' + latex(
        dCnsdnj_pow))

    def __mod_prod_sum(kval, fwd=True, end=None):
        nuv = nu_f if fwd else nu_r
        if kval == Ns:
            if end is None:
                end = Ns - 1
            return Product(Ck[l]**nuv[l, i], (l, 1, end))
        else:
            if end is None:
                end = Ns
            return Product(Ck[l]**nuv[l, i], (l, 1, kval - 1), (l, kval + 1, end))

    def __inner_func(kval, fwd=True):
        nuv = nu_f if fwd else nu_r
        return nuv[kval, i] * Ck[kval] ** (nuv[kval, i] - 1) * __mod_prod_sum(kval, fwd)

    def __create_dRopdnj(fwd=True):
        krate = kf_sym[i] if fwd else kr_sym[i]
        return krate * Sum((dCkdnj + dCnsdnj * KroneckerDelta(k, Ns)) *
                           __inner_func(k, fwd), (k, 1, Ns))

    dRopfdnj = __create_dRopdnj()
    write_eq(diff(Ropf_sym[i], nk[j]), dRopfdnj)

    # we need to simplify each term
    expanded = expand(dRopfdnj, power_base=False, power_exp=False)
    expanded = Add(*[simplify(x) for x in Add.make_args(expanded)])
    dRopfdnj = assert_subs(expanded,
                           (Sum(KroneckerDelta(Ns, k) * __inner_func(k, True), (k, 1, Ns)),
                            __inner_func(Ns, True)),
                           (Sum(KroneckerDelta(k, j) * __inner_func(k, True), (k, 1, Ns)),
                            __inner_func(j, True))
                           )

    dRopfdnj = simplify(dRopfdnj)
    write_eq(diff(Ropf_sym[i], nk[j]), dRopfdnj)

    # define the S terms
    Sfwd = MyIndexedBase(r'S^{\prime}')
    write_eq(Sfwd[l], __inner_func(l, True), sympy=True)
    register_equal(Sfwd[j], __inner_func(j, True))
    register_equal(Sfwd[Ns], __inner_func(Ns, True))
    # and sub in
    dRopfdnj = assert_subs(dRopfdnj, (__inner_func(j, True),
                                      Sfwd[j]), (__inner_func(Ns, True), Sfwd[Ns]))
    write_eq(diff(Ropf_sym[i], nk[j]), dRopfdnj, register=True)

    dRoprdnj = __create_dRopdnj(False)
    write_eq(diff(Ropr_sym[i], nk[j]), dRoprdnj)

    expanded = expand(dRoprdnj, power_base=False, power_exp=False)
    expanded = Add(*[simplify(x) for x in Add.make_args(expanded)])
    dRoprdnj = assert_subs(expanded,
                           (Sum(KroneckerDelta(Ns, k) * __inner_func(k, False), (k, 1, Ns)),
                            __inner_func(Ns, False)),
                           (Sum(KroneckerDelta(k, j) * __inner_func(k, False), (k, 1, Ns)),
                            __inner_func(j, False))
                           )

    dRoprdnj = simplify(dRoprdnj)
    write_eq(diff(Ropr_sym[i], nk[j]), dRoprdnj)

    # define the S terms
    Srev = MyIndexedBase(r'S^{\prime\prime}')
    write_eq(Srev[l], __inner_func(l, False), sympy=True)
    register_equal(Srev[j], __inner_func(j, False))
    register_equal(Srev[Ns], __inner_func(Ns, False))
    # and sub in
    dRoprdnj = assert_subs(dRoprdnj, (__inner_func(j, False),
                                      Srev[j]), (__inner_func(Ns, False), Srev[Ns]))
    write_eq(diff(Ropr_sym[i], nk[j]), dRoprdnj, register=True)
    latexfile.write('For all reversible reactions\n')
    # now do dRop/dnj
    dRopdnj = assert_subs(diff(Rop, nk[j]),
                          (diff(Ropf_sym[i], nk[j]), dRopfdnj),
                          (diff(Ropr_sym[i], nk[j]), dRoprdnj))
    write_eq(diff(Rop_sym[i], nk[j]), dRopdnj, sympy=True, register=True)

    write_section('Temperature Derivative', sub=True)

    write_eq(Ropf_sym, Ropf)
    dkfdT = assert_subs(factor_terms(diff(kf, T)), (kf, kf_sym[i]))
    write_eq(diff(kf_sym[i], T), dkfdT, register=True)

    def get_dr_dt(fwd=True, explicit=True, writetofile=True,
                  plog=False, cheb=False, register=False,
                  sympy=False):
        Ropt_sym = Ropf_sym if fwd else Ropr_sym
        Rop_temp = Ropf if fwd else Ropr
        nuv = nu_f if fwd else nu_r
        Sval = Sfwd if fwd else Srev

        # sub in Cns for proper temperature derivative
        Rop_temp = assert_subs(
            Rop_temp,
            (Product(Ck[k]**nuv[k, i], (k, 1, Ns)),
             Cns**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))))

        if writetofile:
            write_eq(Ropt_sym, Rop_temp)

        dRoptdT = diff(Rop_temp, T)
        if writetofile:
            write_eq(diff(Ropt_sym[i], T), dRoptdT)

        # sub in Ck[Ns]
        dRoptdT = expand_mul(simplify(assert_subs(dRoptdT, (Cns, Ck[Ns]))))

        # and go back original product
        dRoptdT = assert_subs(
            dRoptdT, (Ck[Ns] * Ck[Ns]**(nuv[Ns, i] - 1), Ck[Ns]**nuv[Ns, i]))
        dRoptdT = assert_subs(dRoptdT, (Ck[Ns]**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
                                        Product(Ck[k]**nuv[k, i], (k, 1, Ns))))

        # and sub in C
        dRoptdT = assert_subs(dRoptdT, (Ctot, Ctot_sym))

        if writetofile:
            write_eq(diff(Ropt_sym[i], T), dRoptdT)

        # finally sub in the S term
        # need to modify the inner function to use k as the sum variable
        inner = __inner_func(Ns, fwd=fwd)

        # make sure it's equivalent before we mess with it
        assert_subs(dRoptdT,
                    (inner, Sval[Ns]))

        # switch the sum variable
        inner = assert_subs(inner,
                            (__mod_prod_sum(Ns, fwd=fwd),
                             Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))))
        # and force a subsitution
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

        if not conp:
            # put the ROP back in
            dRoptdT = assert_subs(dRoptdT, (
                Ck[Ns] ** (nuv[Ns, i] + 1) / Ck[Ns], Ck[Ns] ** nuv[Ns, i]),
                (Ck[Ns] ** nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
                    Product(Ck[k]**nuv[k, i], (k, 1, Ns))))

        dRoptdT = assert_subs(dRoptdT, (diff(ksym[i], T), dkdT),
                              (Ropf if fwd else Ropr, Ropt_sym[i]),
                              assumptions=[(diff(ksym[i], T), dkdT)])
        write_eq(diff(Ropt_sym[i], T), dRoptdT,
                 register=register, sympy=sympy)

        return dRoptdT

    dRopfdT = get_dr_dt(register=True)

    latexfile.write(
        'For reactions with explicit reverse Arrhenius coefficients\n')

    # find the reverse derivative
    dkr_rexpdT = assert_subs(factor_terms(diff(kr_rexp, T)), (kr_rexp, kr_sym[i]),
                             assumptions=[(kr_rexp, kr_sym[i])])

    # and the derivative of Rop
    dRopr_rexpdT = get_dr_dt(fwd=False, explicit=True, writetofile=False)

    dRop_expdT = dRopfdT - dRopr_rexpdT
    dRop_expdT = assert_subs(dRop_expdT, (Ropf, Ropf_sym[i]))

    write_eq(diff(Rop_sym[i], T), dRop_expdT,
             enum_conds=reversible_type.explicit)

    latexfile.write('For non-explicit reversible reactions\n')

    def get_dkr_dT(dkfdTval, writetofile=True, plog=True):
        # find dkr/dT
        dkrdT = diff(kf_sym[i] / Kc_sym[i], T)
        if writetofile:
            write_eq(diff(kr_sym[i], T), dkrdT)
        dkrdT = assert_subs(dkrdT, (diff(kf_sym[i], T), dkfdTval),
                            assumptions=[(diff(kf_sym[i], T), dkfdTval)])
        dkrdT = assert_subs(dkrdT, (kf_sym[i] / Kc_sym[i], kr_sym[i]))
        dkrdT = factor_terms(dkrdT)
        if writetofile:
            write_eq(diff(kr_sym[i], T), dkrdT)

        # dkcdT
        dKcdT = diff(Kc, T)
        dKcdT = assert_subs(dKcdT, (Kc, Kc_sym[i]))
        if writetofile:
            write_eq(diff(Kc_sym[i], T), dKcdT)
            register_equal(diff(Kc_sym[i], T), dKcdT)

        # sub into dkrdT
        dkrdT = assert_subs(dkrdT, (diff(Kc_sym[i], T), dKcdT))
        write_eq(diff(kr_sym[i], T), dkrdT)
        return dkrdT

    dkrdT = get_dkr_dT(dkfdT)

    # now the full dRdT
    dRoprdT = get_dr_dt(fwd=False, explicit=False, writetofile=False)

    write_eq(diff(Ropr_sym[i], T), dRoprdT)

    dRop_nonexpdT = assert_subs(diff(Rop, T), (diff(Ropf_sym[i], T), dRopfdT),
                                (diff(Ropr_sym[i], T), dRoprdT),
                                assumptions=[(diff(Ropr_sym[i], T), dRoprdT)])
    write_eq(diff(Rop_sym[i], T), dRop_nonexpdT,
             enum_conds=reversible_type.non_explicit)

    dBkdt = simplify(diff(Bk, T))
    dBkdt = assert_subs(dBkdt, (
        dBkdt, (a[k, 0] - 1 + a[k, 5] / T) / T + Rational(1, 2) * a[k, 1] + T * (
            Rational(1, 3) * a[k, 2] + T * (Rational(1, 4) * a[k, 3] +
                                            Rational(1, 5) * T * a[k, 4]))))

    write_eq(diff(B_sym[k], T), dBkdt, sympy=True)

    # Derivatives of the extra dependent variable
    write_section(r'{} derivatives'.format(extra_var_name), sub=True)

    def __var_creator(deriv_of, wrt):
        return Symbol(r'\frac{{\partial {dof} }}{{\partial {wrt} }}'.format(
            dof=latex(deriv_of), wrt=latex(wrt)))

    if not conp:
        dCkde_sym = __var_creator(Ck[k], extra_var)
    else:
        dCkde_sym = diff(Ck[k], extra_var)

    dCkde = assert_subs(
        diff(assert_subs(Ck[k], (Ck[k], nk[k] / V)), extra_var),
        (nk[k] / V, Ck[k]))

    write_eq(dCkde_sym, dCkde, register=True)

    if not conp:
        dCnsde_sym = __var_creator(Ck[Ns], extra_var)
    else:
        dCnsde_sym = diff(Ck[Ns], extra_var)

    dCnsde = simplify(
        assert_subs(diff(Cns, extra_var),
                    (dCkde_sym, dCkde)))

    register_equal(diff(Cns, extra_var), dCnsde)
    write_eq(dCnsde_sym, dCnsde)

    def __simplify_product_of_powers(arg):
        num, den = fraction(arg)
        numv = next((x for x in Mul.make_args(num) if isinstance(x, Pow)),
                    None)
        if numv is None:
            return arg
        numfunc, numpow = numv.args
        denv = next((x for x in Mul.make_args(den) if x == numfunc or (
            isinstance(x, Pow) and x.args[0] == numfunc)), None)

        if not denv:
            return arg

        if isinstance(denv, Pow):
            retv = numfunc**(numpow - denv.args[1])
        else:
            retv = numfunc**(numpow - 1)
        retv *= Mul(*[x for x in Mul.make_args(num) if x != numv])
        retv /= Mul(*[x for x in Mul.make_args(den) if x != denv])

        assert simplify(retv - arg) == 0
        return retv

    # finally power of Cns
    # come up with equivalence for Ctot - Cns
    shortsum = Sum(Ck[k], (k, 1, Ns - 1))
    val = Ctot - Sum(Ck[k], (k, 1, Ns - 1))
    # ensure iequal to Cns
    assert_subs(val, (val, Cns))
    # turn into form we want
    val = assert_subs(val, (Ctot, Ctot_sym))
    val = solve(Eq(Ck[Ns], val), shortsum)[0]
    register_equal(shortsum, val)

    # take derivative of Cns**nu and sub in above
    dCnsde_pow = assert_subs(
        diff(Cns**nu_f[k, i], extra_var),
        (dCkde_sym, dCkde),
        (Cns, Ck[Ns]))

    dCnsde_pow = assert_subs(
        __simplify_product_of_powers(simplify(dCnsde_pow)),
        (Sum(Ck[k], (k, 1, Ns - 1)), Ctot_sym - Ck[Ns]))

    write_dummy_eq(r'\frac{\partial [C_{Ns}]^{\nu^{\prime}_{Ns, i}}}{\partial '
                   + latex(extra_var) + ' } = ' + latex(dCnsde_pow))

    dCtotde = diff(Ctot, extra_var)
    write_eq(diff(Ctot_sym, extra_var), dCtotde, register=True)

    # store equalities
    register_equal(diff(Cns**nu_f[Ns, i], extra_var), dCnsde_pow)
    dCnsde_pow_rev = assert_subs(dCnsde_pow, (nu_f[Ns, i], nu_r[Ns, i]),
                                 assumptions=[(nu_f[Ns, i], nu_r[Ns, i])])
    register_equal(diff(Cns**nu_r[Ns, i], extra_var), dCnsde_pow_rev)

    def __get_dr_de(fwd=True, writetofile=True):
        Ropv = Ropf if fwd else Ropr
        Ropv_working = Ropf if fwd else Ropr
        Ropv_sym = Ropf_sym[i] if fwd else Ropr_sym[i]
        dRopvdE_sym = diff(Ropv_sym, extra_var)
        nuv = nu_f if fwd else nu_r
        Sval = Sfwd if fwd else Srev

        Ropv_working = assert_subs(Ropv_working, (
            Product(Ck[k]**nuv[k, i], (k, 1, Ns)),
            Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)) * Cns ** nuv[Ns, i]))

        if writetofile:
            write_eq(Ropv_sym, Ropv_working)

        # take diff, sub in derivatives
        dRopvdE = diff(Ropv_working, extra_var)

        # sub in Ck[Ns] and derivatives
        dRopvdE = assert_subs(dRopvdE, (
            Cns, Ck[Ns]))

        # if constant pressure, sub in product rule
        if conp:
            dRopvdE = assert_subs(dRopvdE, (
                diff(Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)), V),
                Sum(diff(Ck[k]**nuv[k, i], V) *
                    __mod_prod_sum(k, fwd=fwd, end=Ns-1), (k, 1, Ns - 1))))

        if writetofile:
            write_eq(dRopvdE_sym, dRopvdE)

        # fix conc derivatives
        dRopvdE = assert_subs(
            dRopvdE,
            (dCkde_sym, dCkde),
            (diff(Cns, extra_var), dCnsde),
            (diff(Cns**nuv[Ns, i], extra_var),
                dCnsde_pow if fwd else dCnsde_pow_rev))

        write_eq(dRopvdE_sym, dRopvdE)

        if conp:
            # put the full product back in
            term = next(term for term in Add.make_args(dRopvdE) if
                        term.has(__mod_prod_sum(k, fwd=fwd, end=Ns-1)))

            # get the specific multplication term
            mterm = next(term for term in Mul.make_args(term)
                         if isinstance(term, Sum))

            # sub in simplified form
            new_mterm = mterm.func(assert_subs(
                mterm.function,
                (Ck[k]**nuv[k, i] * __mod_prod_sum(k, fwd=fwd, end=Ns-1),
                 Product(Ck[l]**nuv[l, i], (l, 1, Ns - 1))),
            ),
                mterm.limits)

            # and go back
            new_term = Mul(*[x if x != mterm else new_mterm
                             for x in Mul.make_args(term)])

            dRopvdE = Add(*[x if x != term else simplify(new_term)
                            for x in Add.make_args(dRopvdE)])

            # shortsum -> previously derived Ctot symbols
            dRopvdE = expand(assert_subs(
                dRopvdE,
                (Sum(Ck[k], (k, 1, Ns - 1)), Ctot_sym - Ck[Ns])))

        if writetofile:
            write_eq(dRopvdE_sym, dRopvdE)

        # next, put in sum simplification
        dRopvdE = Add(*[simplify(__simplify_product_of_powers(x))
                        for x in Add.make_args(dRopvdE)])
        dRopvdE = assert_subs(dRopvdE, (
            Sum(Ck[k], (k, 1, Ns - 1)), Ctot_sym - Ck[Ns]))

        # put the SNs term in
        dRopvdE = Add(*[__simplify_product_of_powers(x)
                        for x in Add.make_args(expand(dRopvdE))])

        # and put in Sns
        dRopvdE = assert_subs(
            dRopvdE,
            (Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
             Product(Ck[l]**nuv[l, i], (l, 1, Ns - 1))),
            (__inner_func(Ns, fwd), Sval[Ns]))

        if writetofile:
            write_eq(dRopvdE_sym, dRopvdE)

        if conp:
            # put in ROP
            dRopvdE = assert_subs(
                dRopvdE,
                (Product(Ck[l]**nuv[l, i], (l, 1, Ns - 1)),
                 Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))),
                (Ck[Ns]**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
                 Product(Ck[k]**nuv[k, i], (k, 1, Ns))),
                (Ropv, Ropv_sym),
                assumptions=[(Ropv_working, Ropv_sym)])

            # and stick nu[ns, i] back into nu sum
            staticterm = Add(*[x for x in Add.make_args(dRopvdE) if x.has(
                Sval[Ns])])
            Ropsum = simplify(Add(*[x for x in Add.make_args(dRopvdE)
                                    if not x.has(Sval[Ns])]))
            Ropsum = assert_subs(
                Ropsum,
                (nuv[Ns, i] + Sum(nuv[k, i], (k, 1, Ns - 1)),
                 Sum(nuv[k, i], (k, 1, Ns))
                 ))
            dRopvdE = Add(*[staticterm, Ropsum])

        return dRopvdE

    dRopfdE = __get_dr_de(True)
    write_eq(diff(Ropf_sym[i], extra_var), dRopfdE, register=True, sympy=True)
    dRoprdE = __get_dr_de(False)
    write_eq(diff(Ropr_sym[i], extra_var), dRoprdE, register=True, sympy=True)
    dRopdE = dRopfdE - dRoprdE

    write_section(r'Third-Body\slash Falloff Derivatives')
    write_section('Elementary reactions\n', sub=True)
    write_eq(diff(ci[i], T), diff(ci_elem, T),
             enum_conds=reaction_type.elementary)
    write_eq(diff(ci[i], nk[j]), diff(
        ci_elem, nk[j]), enum_conds=reaction_type.elementary)

    dci_elemde_sym = diff(ci[i], extra_var)
    write_eq(dci_elemde_sym, diff(
        ci_elem, extra_var), enum_conds=reaction_type.elementary)

    write_section('Third-body enhanced reactions', sub=True)
    dci_thddT = assert_subs(diff(assert_subs(ci_thd, (Ctot_sym, Ctot)), T),
                            (Ctot, Ctot_sym))

    write_eq(diff(ci_thd_sym, T), dci_thddT, enum_conds=reaction_type.thd)

    dci_thddnj = diff(assert_subs(ci_thd,
                                  (Ctot_sym, Ctot),
                                  (Ck[k], nk[k] / V)),
                      nk[j])
    dci_thddnj = assert_subs(simplify(dci_thddnj),
                             (Sum((-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i]) *
                                  KroneckerDelta(j, k), (k, 1, Ns - 1)),
                                 -thd_bdy_eff[Ns, i] + thd_bdy_eff[j, i]),
                             (Cns_sym, Ck[Ns]))

    write_eq(diff(ci_thd_sym, nk[j]), dci_thddnj,
             enum_conds=[reaction_type.thd, thd_body_type.mix])

    dci_thdde = diff(assert_subs(ci_thd,
                                 (Ctot_sym, Ctot)),
                     extra_var)
    dci_thdde = assert_subs(dci_thdde,
                            (Ctot, Ctot_sym))
    if conp:
        dci_thdde = assert_subs(dci_thdde,
                                (diff(Ck[k], extra_var), dCkde))
        # express in terms of Xi
        sub_in = Sum(
            (-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i]) * Ck[k], (k, 1, Ns - 1))
        sub_in_eq = solve(Eq(ci_thd_sym, ci_thd), sub_in)[0]
        dci_thdde = simplify(dci_thdde)
        dci_thdde = assert_subs(dci_thdde,
                                (simplify(-sub_in), -sub_in_eq),
                                assumptions=[(simplify(-sub_in), -sub_in_eq)])

    write_eq(diff(ci_thd_sym, extra_var), dci_thdde,
             enum_conds=[reaction_type.thd, thd_body_type.mix])

    latexfile.write(r'For species $m$ as the third-body' + '\n')
    dci_spec_dT = assert_subs(diff(assert_subs(ci_thd_species, (
        Ctot_sym, Ctot)), T), (Ctot, Ctot_sym))
    write_eq(diff(ci[i], T), dci_spec_dT,
             enum_conds=[reaction_type.thd, thd_body_type.species])

    register_equal(Ck[m], nk[m] / V)
    dci_spec_dnj = diff(assert_subs(ci_thd_species, (
        Ck[m], nk[m] / V), (
        Ck[k], nk[k] / V)),
        nk[j])

    # kill derivatives of m
    dci_spec_dnj = assert_subs(dci_spec_dnj, (
        diff(m, nk[j]), S.Zero),
        assumptions=[(diff(m, nk[j]), S.Zero)])

    # and fix sum
    dci_spec_dnj = assert_subs(simplify(dci_spec_dnj), (
        Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), S.One))

    write_eq(diff(ci[i], nk[j]), dci_spec_dnj)

    # and eliminate the Delta(m, Ns, j) as it's never true
    dci_spec_dnj = assert_subs(dci_spec_dnj, (
        KroneckerDelta(Ns, m) * KroneckerDelta(j, m), S.Zero),
        (Cns_sym, Ck[Ns]),
        assumptions=[(KroneckerDelta(Ns, m) * KroneckerDelta(j, m), S.Zero)])

    write_eq(diff(ci[i], nk[j]), dci_spec_dnj,
             enum_conds=[reaction_type.thd, thd_body_type.species])

    # and extra variable
    dci_spec_de = diff(ci_thd_species, extra_var)
    if not conp:
        dci_spec_de = assert_subs(
            dci_spec_de,
            (diff(Ctot_sym, extra_var), dCtotde),)
    else:
        dCkmde = assert_subs(dCkde, (k, m),
                             assumptions=[(k, m)])
        register_equal(diff(Ck[m], extra_var), dCkmde)
        dci_spec_de = assert_subs(
            dci_spec_de,
            (diff(Ck[k], extra_var), dCkde),
            (diff(Ck[m], extra_var), dCkmde)
        )

        write_eq(diff(ci[i], extra_var), dci_spec_de)
        dci_spec_de = assert_subs(
            Add(*[simplify(x) for x in Add.make_args(dci_spec_de)]),
            (Sum(Ck[k], (k, 1, Ns - 1)), Ctot_sym - Ck[Ns]),
        )

    write_eq(diff(ci[i], extra_var), dci_spec_de,
             enum_conds=[reaction_type.thd, thd_body_type.species])

    latexfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    dci_unity_dT = assert_subs(diff(Ctot, T),
                               (Ctot, Ctot_sym))

    write_eq(diff(ci[i], T), dci_unity_dT,
             enum_conds=[reaction_type.thd, thd_body_type.unity])

    dci_unity_dnj = diff(Ctot, nk[j])
    write_eq(diff(ci[i], nk[j]), dci_unity_dnj,
             enum_conds=[reaction_type.thd, thd_body_type.unity])

    dci_unity_de = diff(Ctot, extra_var)
    write_eq(diff(ci[i], extra_var), dci_unity_de,
             enum_conds=[reaction_type.thd, thd_body_type.unity])

    write_section('Unimolecular/recombination fall-off reactions', sub=True)
    dci_falldT = factor_terms(
        collect(
            assert_subs(diff(ci_fall, T),
                        (ci_fall, ci[i]),
                        assumptions=[(ci_fall, ci[i])]),
            diff(Pri_sym, T)))
    write_eq(diff(ci[i], T), dci_falldT,
             enum_conds=reaction_type.fall)

    dci_falldnj = factor_terms(
        collect(
            assert_subs(diff(ci_fall, nk[j]),
                        (ci_fall, ci[i]),
                        assumptions=[(ci_fall, ci[i])]),
            diff(Pri_sym, nk[j]) / (Pri_sym + 1)))
    write_eq(diff(ci[i], nk[j]), dci_falldnj,
             enum_conds=reaction_type.fall)

    dci_fallde = factor_terms(
        collect(
            assert_subs(diff(ci_fall, extra_var),
                        (ci_fall, ci[i]),
                        assumptions=[(ci_fall, ci[i])]),
            diff(Pri_sym, extra_var) / (Pri_sym + 1)))
    write_eq(diff(ci[i], extra_var), dci_fallde,
             enum_conds=reaction_type.fall)

    write_section('Chemically-activated bimolecular reactions', sub=True)
    dci_chemdT = factor_terms(
        collect(
            assert_subs(diff(ci_chem, T), (ci_chem, ci[i]),
                        assumptions=[(ci_chem, ci[i])]),
            diff(Pri_sym, T)))
    write_eq(diff(ci[i], T), dci_chemdT,
             enum_conds=reaction_type.chem)

    dci_chemdnj = factor_terms(
        collect(
            assert_subs(diff(ci_chem, nk[j]), (ci_chem, ci[i]),
                        assumptions=[(ci_chem, ci[i])]),
            diff(Pri_sym, nk[j]) / (Pri_sym + 1)))
    write_eq(diff(ci[i], nk[j]), dci_chemdnj,
             enum_conds=reaction_type.chem)

    dci_chemde = factor_terms(
        collect(
            assert_subs(diff(ci_chem, extra_var), (ci_chem, ci[i]),
                        assumptions=[(ci_chem, ci[i])]),
            diff(Pri_sym, extra_var) / (Pri_sym + 1)))
    write_eq(diff(ci[i], extra_var), dci_chemde,
             enum_conds=reaction_type.chem)

    write_section(r'Reduced Pressure derivatives', sub=True)

    def __get_pri_fac_terms(dPri_dT, dPri_dnj, dPri_de, descriptor):
        # simplify the dPri/dT term
        # find terms with Pr in them
        dPri_dT_prifac = Add(
            *[x for x in Add.make_args(dPri_dT) if x.has(Pri_sym)])
        dPri_dT_prifac = dPri_dT_prifac / Pri_sym
        dPri_dT_prifac_sym = Symbol(
            r'\Theta_{{P_{{r,i}}, \partial T, {}}}'.format(descriptor))
        register_equal(dPri_dT_prifac_sym, dPri_dT_prifac)

        # and the non Pr terms
        dPri_dT_noprifac = Add(
            *[x for x in Add.make_args(dPri_dT) if not x.has(Pri_sym)])
        dPri_dT_noprifac_sym = Symbol(
            r'\bar{{\theta}}_{{P_{{r, i}}, \partial T, {}}}'.format(descriptor))
        register_equal(dPri_dT_noprifac_sym, dPri_dT_noprifac)

        # now do the dPri/dnj term
        dPri_dnj_fac = dPri_dnj / (k0_sym / (kinf_sym * V))
        dPri_dnj_fac_sym = Symbol(
            r'\bar{{\theta}}_{{P_{{r, i}}, \partial n_j, {}}}'.format(descriptor))
        register_equal(dPri_dnj_fac_sym, dPri_dnj_fac)

        # simplify dPri/dExtra term

        dPri_de_prifac = Add(
            *[x for x in Add.make_args(dPri_de) if x.has(Pri_sym)])
        dPri_de_prifac = dPri_de_prifac / Pri_sym
        dPri_de_prifac_sym = Symbol(
            r'\Theta_{{P_{{r,i}}, \partial {}, {}}}'.format(extra_var, descriptor))
        register_equal(dPri_de_prifac_sym, dPri_de_prifac)

        dPri_de_noprifac = Add(
            *[x for x in Add.make_args(dPri_de) if not x.has(Pri_sym)])
        dPri_de_noprifac_sym = Symbol(
            r'\bar{{\theta}}_{{P_{{r, i}}, \partial {}, {}}}'.format(extra_var, descriptor))
        register_equal(dPri_de_noprifac_sym, dPri_de_noprifac)

        # and sub in
        dPri_dT = assert_subs(dPri_dT, (dPri_dT_prifac, dPri_dT_prifac_sym),
                              (dPri_dT_noprifac, dPri_dT_noprifac_sym))
        dPri_dnj = assert_subs(dPri_dnj, (dPri_dnj_fac, dPri_dnj_fac_sym))
        dPri_de = assert_subs(dPri_de, (dPri_de_noprifac, dPri_de_noprifac_sym),
                              (dPri_de_prifac, dPri_de_prifac_sym))

        # write the substituted forms
        write_eq(diff(Pri_sym, T), dPri_dT)
        write_eq(diff(Pri_sym, nk[j]), dPri_dnj)
        write_eq(diff(Pri_sym, extra_var), dPri_de)

        write_eq(dPri_dT_prifac_sym, dPri_dT_prifac)
        write_eq(dPri_dT_noprifac_sym, dPri_dT_noprifac)
        write_eq(dPri_dnj_fac_sym, dPri_dnj_fac)
        write_eq(dPri_de_prifac_sym, dPri_de_prifac)
        write_eq(dPri_de_noprifac_sym, dPri_de_noprifac)

        return dPri_dT, dPri_dT_prifac, dPri_dT_prifac_sym, dPri_dT_noprifac,\
            dPri_dT_noprifac_sym, dPri_dnj, dPri_dnj_fac, dPri_dnj_fac_sym,\
            dPri_de, dPri_de_prifac, dPri_de_prifac_sym, dPri_de_noprifac,\
            dPri_de_noprifac_sym

    latexfile.write('\nFor the mixture as the third body\n')
    dPri_mixdT = assert_subs(diff(Pri_mix, T), (diff(ci_thd_sym, T), dci_thddT),
                             assumptions=[(diff(ci_thd_sym, T), dci_thddT)])
    A_inf, Beta_inf = symbols(r'A_{\infty} \beta_{\infty}')
    Ea_inf = Symbol(r'E_{a, \infty}')

    A_0, Beta_0 = symbols(r'A_{0} \beta_{0}')
    Ea_0 = Symbol('E_{a, 0}')

    dkinfdT = assert_subs(dkfdT, (A[i], A_inf),
                          (Beta[i], Beta_inf), (Ea[i], Ea_inf),
                          (kf_sym[i], kinf_sym),
                          assumptions=[(A[i], A_inf),
                                       (Beta[i], Beta_inf), (Ea[i], Ea_inf),
                                       (kf_sym[i], kinf_sym)
                                       ])
    register_equal(diff(kinf_sym, T), dkinfdT)
    dk0dT = assert_subs(dkfdT, (A[i], Symbol(r'A_{0}')),
                        (Beta[i], Symbol(r'\beta_{0}')), (Ea[
                            i], Symbol(r'E_{a, 0}')),
                        (kf_sym[i], k0_sym),
                        assumptions=[(A[i], Symbol(r'A_{0}')),
                                     (Beta[i], Symbol(r'\beta_{0}')
                                      ), (Ea[i], Symbol(r'E_{a, 0}')),
                                     (kf_sym[i], k0_sym)
                                     ])
    register_equal(diff(k0_sym, T), dk0dT)
    dPri_mixdT = assert_subs(dPri_mixdT, (diff(k0_sym, T), dk0dT),
                             (diff(kinf_sym, T), dkinfdT))
    dPri_mixdT = assert_subs(collect(dPri_mixdT, Pri_mix / T), (Pri_mix, Pri_sym),
                             assumptions=[(Pri_mix, Pri_sym)])
    write_eq(diff(Pri_sym, T), dPri_mixdT)

    dPri_mixdnj = assert_subs(diff(Pri_mix, nk[j]), (diff(ci_thd_sym, nk[j]), dci_thddnj),
                              assumptions=[(diff(ci_thd_sym, nk[j]), dci_thddnj)])
    dPri_mixdnj = assert_subs(dPri_mixdnj, (Sum((-thd_bdy_eff[Ns, i] + thd_bdy_eff[k, i])
                                                * KroneckerDelta(j, k), (k, 1, Ns - 1)),
                                            -thd_bdy_eff[Ns, i] + thd_bdy_eff[j, i]))
    write_eq(diff(Pri_sym, nk[j]), dPri_mixdnj)

    dPri_mixde = assert_subs(diff(Pri_mix, extra_var),
                             (diff(ci_thd_sym, extra_var), dci_thdde),
                             assumptions=[(diff(ci_thd_sym, extra_var), dci_thdde)])
    dPri_mixde = assert_subs(expand(dPri_mixde),
                             (Pri_mix, Pri_sym),
                             assumptions=[(Pri_mix, Pri_sym)])

    write_eq(diff(Pri_sym, extra_var), dPri_mixde)

    latexfile.write('Simplifying:\n')
    dPri_mixdT, dPri_mixdT_prifac, dPri_mixdT_prifac_sym, dPri_mixdT_noprifac,\
        dPri_mixdT_noprifac_sym, dPri_mixdnj, dPri_mixdnj_fac, \
        dPri_mixdnj_fac_sym, dPri_mixde, dPri_mixde_prifac, \
        dPri_mixde_prifac_sym, dPri_mixde_noprifac, \
        dPri_mixde_noprifac_sym = __get_pri_fac_terms(
            dPri_mixdT, dPri_mixdnj, dPri_mixde, "mix")

    latexfile.write('For species $m$ as the third-body\n')

    dPri_specdT = assert_subs(diff(assert_subs(Pri_spec, (
        Ctot_sym, Ctot)), T), (
        Ctot, Ctot_sym)
    )
    dPri_specdT = assert_subs(dPri_specdT, (diff(k0_sym, T), dk0dT),
                              (diff(kinf_sym, T), dkinfdT))
    dPri_specdT = assert_subs(collect(dPri_specdT, Pri_spec / T), (Pri_spec, Pri_sym),
                              assumptions=[(Pri_spec, Pri_sym)])
    write_eq(diff(Pri_sym, T), dPri_specdT)

    dPri_specdnj = assert_subs(
        diff(assert_subs(
            Pri_spec,
            (Ck[m], nk[m] / V),
            (Ck[k], nk[k] / V),
            (Ctot_sym, Ctot)), nk[j]),
        (diff(ci[i], nk[j]), dci_spec_dnj),
        (diff(m, nk[j]), S.Zero),
        assumptions=[(diff(ci[i], nk[j]), dci_spec_dnj),
                     (diff(m, nk[j]), S.Zero)])
    # do kronecker delta / simplification
    dPri_specdnj = assert_subs(simplify(dPri_specdnj), (
        Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), S.One), (
        KroneckerDelta(j, m) * KroneckerDelta(Ns, m), S.Zero
    ),
        assumptions=[(KroneckerDelta(j, m) * KroneckerDelta(Ns, m), S.Zero)]
    )
    write_eq(diff(Pri_sym, nk[j]), dPri_specdnj)

    dPri_specde = diff(
        assert_subs(
            Pri_spec,
            (ci_thd_species, ci[i]),
            assumptions=[(ci_thd_species, ci[i])]), extra_var)
    dPri_specde = assert_subs(
        dPri_specde,
        (diff(ci[i], extra_var),
         dci_spec_de),
        assumptions=[(diff(ci[i], extra_var),
                      dci_spec_de)]
    )

    # recover Pri

    # collect Cns and Cm terms
    dPri_specde = collect(expand(dPri_specde),
                          (Ck[m], Ck[Ns]))

    # and simplify each term
    dPri_specde = __simplify_per_term(dPri_specde)

    # sub in Cns, and Pri
    dPri_specde = assert_subs(
        dPri_specde,
        (Ck[Ns], Cns),
        (Ctot, Ctot_sym)
    )

    # collect k0 / kinf / V for terms with Ck or Cm
    if conp:
        pr_term, nopr_term = __separate_on(dPri_specde, (Ck[m], Ck[k]))
        pr_term = collect(pr_term, k0_sym / (kinf_sym * V))
        pr_term = assert_subs(
            pr_term,
            (pr_term * V, -Pri_spec))
        pr_term = assert_subs(
            pr_term,
            (Pri_spec, Pri_sym),
            assumptions=[(Pri_spec, Pri_sym)]
        )
        dPri_specde = Add(*[pr_term, nopr_term])

    write_eq(diff(Pri_sym, extra_var), dPri_specde)

    latexfile.write('Simplifying:\n')
    dPri_specdT, dPri_specdT_prifac, dPri_specdT_prifac_sym,\
        dPri_specdT_noprifac, dPri_specdT_noprifac_sym, dPri_specdnj,\
        dPri_specdnj_fac, dPri_specdnj_fac_sym, dPri_specde,\
        dPri_specde_prifac, dPri_specde_prifac_sym, dPri_specde_noprifac, \
        dPri_specde_noprifac_sym = __get_pri_fac_terms(
            dPri_specdT, dPri_specdnj, dPri_specde, "spec")
    latexfile.write(r'If all $\alpha_{j, i} = 1$ for all species j' + '\n')
    Pri_unity_sym = assert_subs(Pri_unity, (Ctot, Ctot_sym))
    register_equal(Pri_unity_sym, Pri_unity)
    dPri_unitydT = diff(assert_subs(Pri_unity, (Ctot_sym, Ctot)), T)
    dPri_unitydT = assert_subs(dPri_unitydT, (diff(k0_sym, T), dk0dT),
                               (diff(kinf_sym, T), dkinfdT), (Ctot, Ctot_sym))

    dPri_unitydT = assert_subs(collect(dPri_unitydT, Pri_unity_sym / T),
                               (Pri_unity_sym, Pri_sym),
                               (Ctot, Ctot_sym),
                               assumptions=[(Pri_unity_sym, Pri_sym)])
    write_eq(diff(Pri_sym, T), dPri_unitydT)

    dPri_unitydnj = diff(Pri_unity, nk[j])
    write_eq(diff(Pri_sym, nk[j]), dPri_unitydnj)

    dPri_unityde = diff(Pri_unity, extra_var)
    write_eq(diff(Pri_sym, nk[j]), dPri_unityde)

    latexfile.write('Simplifying:\n')
    dPri_unitydT, dPri_unitydT_prifac, dPri_unitydT_prifac_sym,\
        dPri_unitydT_noprifac, dPri_unitydT_noprifac_sym, dPri_unitydnj,\
        dPri_unitydnj_fac, dPri_unitydnj_fac_sym, dPri_unityde,\
        dPri_unityde_prifac, dPri_unityde_prifac_sym, dPri_unityde_noprifac, \
        dPri_unityde_noprifac_sym = __get_pri_fac_terms(
            dPri_unitydT, dPri_unitydnj, dPri_unityde, "unity")

    # finally we make a generic version for simplification
    latexfile.write('Thus we write:\n')
    dPri_dT_prifac_sym = Symbol(r'\Theta_{P_{r,i}, \partial T}')
    dPri_dT_noprifac_sym = Symbol(r'\bar{\theta}_{P_{r, i}, \partial T}')
    dPri_dnj_fac_sym = Symbol(r'\bar{\theta}_{P_{r, i}, \partial n_j}')
    dPri_de_prifac_sym = Symbol(
        r'\Theta_{{P_{{r,i}}, \partial {}}}'.format(extra_var))
    dPri_de_noprifac_sym = Symbol(
        r'\bar{{\theta}}_{{P_{{r, i}}, \partial {}}}'.format(extra_var))
    dPri_dT = assert_subs(dPri_mixdT, (dPri_mixdT_prifac_sym, dPri_dT_prifac_sym),
                          (dPri_mixdT_noprifac_sym, dPri_dT_noprifac_sym),
                          assumptions=[(dPri_mixdT_prifac_sym, dPri_dT_prifac_sym),
                                       (dPri_mixdT_noprifac_sym, dPri_dT_noprifac_sym)])
    dPri_dnj = assert_subs(dPri_mixdnj, (dPri_mixdnj_fac_sym, dPri_dnj_fac_sym),
                           assumptions=[(dPri_mixdnj_fac_sym, dPri_dnj_fac_sym)])
    dPri_de = assert_subs(dPri_mixde, (dPri_mixde_prifac_sym, dPri_de_prifac_sym),
                          (dPri_mixde_noprifac_sym, dPri_de_noprifac_sym),
                          assumptions=[(dPri_mixde_prifac_sym, dPri_de_prifac_sym),
                                       (dPri_mixde_noprifac_sym, dPri_de_noprifac_sym)])

    write_eq(diff(Pri_sym, T), dPri_dT, register=True)
    write_eq(diff(Pri_sym, nk[j]), dPri_dnj, register=True)
    write_eq(diff(Pri_sym, extra_var), dPri_de, register=True)

    latexfile.write('For\n')
    write_cases(dPri_dT_prifac_sym, [(dPri_mixdT_prifac, "mix"),
                                     (dPri_specdT_prifac, "species"),
                                     (dPri_unitydT_prifac, "unity")])
    write_cases(dPri_dT_noprifac_sym, [(dPri_mixdT_noprifac, "mix"),
                                       (dPri_specdT_noprifac, "species"),
                                       (dPri_unitydT_noprifac, "unity")])
    write_cases(dPri_dnj_fac_sym, [(dPri_mixdnj_fac, "mix"),
                                   (dPri_specdnj_fac, "species"),
                                   (dPri_unitydnj_fac, "unity")])
    write_cases(dPri_de_prifac_sym, [(dPri_mixde_prifac, "mix"),
                                     (dPri_specde_prifac, "species"),
                                     (dPri_unityde_prifac, "unity")])
    write_cases(dPri_de_noprifac_sym, [(dPri_mixde_noprifac, "mix"),
                                       (dPri_specde_noprifac, "species"),
                                       (dPri_unityde_noprifac, "unity")])

    write_section('Falloff Blending Factor derivatives', sub=True)
    latexfile.write('\n For Lindemann reactions\n')

    dFi_linddT = diff(Fi_lind, T)
    dFi_linddnj = diff(Fi_lind, nk[j])
    dFi_lindde = diff(Fi_lind, extra_var)
    write_conditional(
        diff(Fi_sym, T), dFi_linddT, enum_conds=falloff_form.lind)
    write_conditional(
        diff(Fi_sym, nk[j]), dFi_linddnj, enum_conds=falloff_form.lind)
    write_conditional(
        diff(Fi_sym, extra_var), dFi_lindde, enum_conds=falloff_form.lind)

    latexfile.write('For Troe reactions\n')
    dFi_troedT = diff(Fi_troe_sym, T)
    dFi_troednj = diff(Fi_troe_sym, nk[j])
    dFi_troede = diff(Fi_troe_sym, extra_var)
    write_conditional(
        diff(Fi_sym, T), dFi_troedT, enum_conds=falloff_form.troe)
    write_conditional(
        diff(Fi_sym, nk[j]), dFi_troednj, enum_conds=falloff_form.troe)
    write_conditional(
        diff(Fi_sym, extra_var), dFi_troede, enum_conds=falloff_form.troe)

    latexfile.write('where\n')
    dFi_troedFcent = assert_subs(factor_terms(
        diff(Fi_troe, Fcent_sym)), (Fi_troe, Fi_troe_sym))
    write_eq(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent,
             register=True, sympy=True)

    dFcentdT = diff(Fcent, T)
    write_eq(diff(Fcent_sym, T), dFcentdT, register=True, sympy=True)

    dFi_troedPri = factor_terms(
        assert_subs(diff(Fi_troe, Pri_sym),
                    (Fi_troe, Fi_troe_sym)))
    write_eq(diff(Fi_troe_sym, Pri_sym), dFi_troedPri)

    latexfile.write('And\n')
    dAtroedFcent = diff(Atroe, Fcent_sym)
    dBtroedFcent = diff(Btroe, Fcent_sym)
    dAtroedPri = diff(Atroe, Pri_sym)
    dBtroedPri = diff(Btroe, Pri_sym)
    write_eq(diff(Atroe_sym, Fcent_sym), dAtroedFcent, register=True)
    write_eq(diff(Btroe_sym, Fcent_sym), dBtroedFcent, register=True)
    write_eq(diff(Atroe_sym, Pri_sym), dAtroedPri, register=True)
    write_eq(diff(Btroe_sym, Pri_sym), dBtroedPri, register=True)

    latexfile.write('Thus\n')
    dFi_troedFcent = factor_terms(simplify(
        assert_subs(dFi_troedFcent,
                    (diff(Atroe_sym, Fcent_sym), dAtroedFcent),
                    (diff(Btroe_sym, Fcent_sym), dBtroedFcent)
                    )))
    write_eq(diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent, register=True)

    dFi_troedPri = factor_terms(
        assert_subs(dFi_troedPri,
                    (diff(Atroe_sym, Pri_sym), dAtroedPri),
                    (diff(Btroe_sym, Pri_sym), dBtroedPri))
    )
    write_eq(diff(Fi_troe_sym, Pri_sym), dFi_troedPri, register=True)

    latexfile.write('And\n')
    dFi_troedT = assert_subs(dFi_troedT, (diff(Fi_troe_sym, Pri_sym), dFi_troedPri),
                             (diff(Fi_troe_sym, Fcent_sym), dFi_troedFcent),
                             (diff(Pri_sym, T), dPri_dT))
    dFi_troedT = simplify(dFi_troedT)

    dFi_troedT_fac = dFi_troedT / Fi_troe_sym

    # used many places
    dFi_dT_fac_sym = Symbol(r'\Theta_{F_i, \partial T}')
    dFi_dnj_fac_sym = Symbol(r'\Theta_{F_i, \partial n_j}')
    dFi_de_fac_sym = Symbol(r'\Theta_{{F_i, \partial {}}}'.format(extra_var))

    dFi_troedT = assert_subs(dFi_troedT, (dFi_troedT_fac, dFi_dT_fac_sym),
                             assumptions=[(dFi_troedT_fac, dFi_dT_fac_sym)])
    write_eq(diff(Fi_sym, T), dFi_troedT)

    dFi_troednj = assert_subs(dFi_troednj, (diff(Fi_troe_sym, Pri_sym), dFi_troedPri),
                              (diff(Pri_sym, nk[j]), dPri_dnj))
    dFi_troednj = __complex_collect(
        simplify(dFi_troednj), Fi_troe_sym * dPri_dnj)
    dFi_troednj_fac = dFi_troednj / (Fi_troe_sym * dPri_dnj)

    dFi_troednj = assert_subs(dFi_troednj, (dFi_troednj_fac, dFi_dnj_fac_sym),
                              assumptions=[(dFi_troednj_fac, dFi_dnj_fac_sym)])
    write_eq(diff(Fi_sym, nk[j]), dFi_troednj)

    dFi_troede = assert_subs(dFi_troede, (diff(Fi_troe_sym, Pri_sym), dFi_troedPri),
                             (diff(Pri_sym, extra_var), dPri_de))
    dFi_troede = simplify(dFi_troede)
    dFi_troede_fac = dFi_troede / Fi_troe_sym

    dFi_troede = assert_subs(dFi_troede, (dFi_troede_fac, dFi_de_fac_sym),
                             assumptions=[(dFi_troede_fac, dFi_de_fac_sym)])

    write_eq(diff(Fi_sym, extra_var), dFi_troede)

    latexfile.write('Where\n')
    write_eq(dFi_dT_fac_sym, dFi_troedT_fac)
    write_eq(dFi_dnj_fac_sym, dFi_troednj_fac)
    write_eq(dFi_de_fac_sym, dFi_troede_fac)

    latexfile.write('For SRI reactions\n')
    dFi_sridT = factor_terms(
        assert_subs(diff(Fi_sri, T), (Fi_sri, Fi_sym),
                    assumptions=[(Fi_sri, Fi_sym)]))
    dFi_sridnj = assert_subs(diff(Fi_sri, nk[j]),
                             (Fi_sri, Fi_sym),
                             assumptions=[(Fi_sri, Fi_sym)])
    dFi_sride = assert_subs(diff(Fi_sri, extra_var),
                            (Fi_sri, Fi_sym),
                            assumptions=[(Fi_sri, Fi_sym)])
    write_eq(diff(Fi_sym, T), dFi_sridT)
    write_eq(diff(Fi_sym, nk[j]), dFi_sridnj)
    write_eq(diff(Fi_sym, extra_var), dFi_sride)

    latexfile.write('Where\n')
    dXdPri = assert_subs(diff(X, Pri_sym), (X, X_sym))
    write_eq(diff(X_sym, Pri_sym), dXdPri, register=True)

    write_eq(
        r'\frac{\partial X}{\partial n_j} = ' + latex(diff(X_sym, nk[j])))

    latexfile.write('And\n')
    dFi_sridT = simplify(
        assert_subs(dFi_sridT, (diff(X_sym, Pri_sym), dXdPri),
                    (diff(Pri_sym, T), dPri_dT)))

    dFi_sridT_fac = dFi_sridT / Fi_sym
    dFi_sridT = assert_subs(dFi_sridT, (dFi_sridT_fac, dFi_dT_fac_sym),
                            assumptions=[(dFi_sridT_fac, dFi_dT_fac_sym)])
    write_eq(diff(Fi_sym, T), dFi_sridT)

    dFi_sridnj = simplify(
        assert_subs(dFi_sridnj, (diff(X_sym, Pri_sym), dXdPri),
                    (diff(Pri_sym, nk[j]), dPri_dnj)))
    dFi_sridnj = __complex_collect(dFi_sridnj, Fi_sym * dPri_dnj)

    dFi_sridnj_fac = dFi_sridnj / (Fi_sym * dPri_dnj)
    dFi_sridnj = assert_subs(dFi_sridnj, (dFi_sridnj_fac, dFi_dnj_fac_sym),
                             assumptions=[(dFi_sridnj_fac, dFi_dnj_fac_sym)])
    write_eq(diff(Fi_sym, nk[j]), dFi_sridnj)

    dFi_sride = simplify(
        assert_subs(dFi_sride, (diff(X_sym, Pri_sym), dXdPri),
                    (diff(Pri_sym, extra_var), dPri_de)))

    dFi_sride_fac = dFi_sride / Fi_sym
    dFi_sride = assert_subs(dFi_sride, (dFi_sride_fac, dFi_de_fac_sym),
                            assumptions=[(dFi_sride_fac, dFi_de_fac_sym)])
    write_eq(diff(Fi_sym, extra_var), dFi_sride)

    latexfile.write('Where\n')
    write_eq(dFi_dT_fac_sym, dFi_sridT_fac)
    write_eq(dFi_dnj_fac_sym, dFi_sridnj_fac)
    write_eq(dFi_de_fac_sym, dFi_sride_fac)

    latexfile.write('Simplifying:\n')
    dFi_dT = assert_subs(dFi_troedT,
                         (Fi_troe_sym, Fi_sym),
                         assumptions=[(Fi_troe_sym, Fi_sym)])
    write_eq(diff(Fi_sym, T), dFi_dT, register=True)

    dFi_dnj = assert_subs(dFi_troednj,
                          (Fi_troe_sym, Fi_sym),
                          assumptions=[(Fi_troe_sym, Fi_sym)])
    write_eq(diff(Fi_sym, nk[j]), dFi_dnj, register=True)

    dFi_de = assert_subs(dFi_troede,
                         (Fi_troe_sym, Fi_sym),
                         assumptions=[(Fi_troe_sym, Fi_sym)])
    write_eq(diff(Fi_sym, extra_var), dFi_de, register=True)

    latexfile.write('Where:\n')

    dFi_linddT_fac = dFi_linddT / Fi_sym
    write_cases(dFi_dT_fac_sym, [(dFi_linddT_fac, 'Lindemann'),
                                 (dFi_troedT_fac, 'Troe'),
                                 (dFi_sridT_fac, 'SRI')])

    dFi_linddnj_fac = dFi_linddnj / Fi_sym
    write_cases(dFi_dnj_fac_sym, [(dFi_linddnj_fac, 'Lindemann'),
                                  (dFi_troednj_fac, 'Troe'),
                                  (dFi_sridnj_fac, 'SRI')])

    dFi_lindde_fac = dFi_lindde / Fi_sym
    write_cases(dFi_de_fac_sym, [(dFi_lindde_fac, 'Lindemann'),
                                 (dFi_troede_fac, 'Troe'),
                                 (dFi_sride_fac, 'SRI')])

    write_section(
        'Unimolecular/recombination fall-off reactions (complete)', sub=True)

    def __subs_ci_terms(dci_dT, dci_dnj, dci_de, ci_term):
        dci_dT = assert_subs(expand(
            assert_subs(dci_dT,
                            (diff(Fi_sym, T), dFi_dT),
                        (diff(Pri_sym, T), dPri_dT))),
            (ci_term, ci[i]),
            assumptions=[(ci_term, ci[i])])
        dci_dT = factor_terms(collect(dci_dT,
                                      [ci[i], Pri_sym]))

        dci_dnj = assert_subs(
            expand(assert_subs(dci_dnj, (diff(Fi_sym, nk[j]), dFi_dnj),
                               (diff(Pri_sym, nk[j]), dPri_dnj))),
            (ci_term, ci[i]),
            assumptions=[(ci_term, ci[i])])
        dci_dnj = factor_terms(collect(dci_dnj,
                                       [dPri_dnj, Fi_sym]))

        dci_de = assert_subs(
            expand(assert_subs(dci_de, (diff(Fi_sym, extra_var), dFi_de),
                               (diff(Pri_sym, extra_var), dPri_de))),
            (ci_term, ci[i]),
            assumptions=[(ci_term, ci[i])])
        dci_de = factor_terms(collect(dci_de,
                                      [ci[i], Pri_sym, dPri_de_prifac_sym]))
        write_eq(diff(ci[i], T), dci_dT)
        write_eq(diff(ci[i], nk[j]), dci_dnj)
        write_eq(diff(ci[i], extra_var), dci_de)
        return dci_dT, dci_dnj, dci_de

    dci_falldT, dci_falldnj, dci_fallde = __subs_ci_terms(
        dci_falldT, dci_falldnj, dci_fallde, ci_fall)

    write_section(
        'Chemically-activated bimolecular reactions (complete)', sub=True)

    dci_chemdT, dci_chemdnj, dci_chemde = __subs_ci_terms(
        dci_chemdT, dci_chemdnj, dci_chemde, ci_chem)

    write_section('Pressure-dependent reaction derivatives')
    latexfile.write('For PLog reactions\n')
    dkf_pdepdT = diff(kf_pdep, T)
    # since the kf_pdep is expressed as a log
    # we need to solve for this in terms of dkf/dT
    mul_term = diff(kf_sym[i], T) / diff(log(kf_sym[i]), T)
    dkf_pdepdT = dkf_pdepdT * mul_term
    write_eq(diff(kf_sym[i], T), dkf_pdepdT)
    # next sub in the corresponding kf derivatives
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

    write_eq(diff(kf_sym[i], T), dkf_pdepdT)

    # and even futher
    dkf_pdepdT = factor_terms(dkf_pdepdT)
    write_eq(diff(kf_sym[i], T), dkf_pdepdT)

    # assemble the Rop derivatives
    dRopf_pdepdT = get_dr_dt(plog=True, writetofile=False)
    dkr_pdepdT = get_dkr_dT(dkf_pdepdT, writetofile=False)
    dRopr_pdepdT = get_dr_dt(plog=True, fwd=False, writetofile=False)
    dRop_pdepdT = dRopf_pdepdT - dRopr_pdepdT

    # transfer dkf_pdepdT / kf_sym for a temporary variable for simplification

    dRop_pdepdT = __complex_collect(dRop_pdepdT, dkf_pdepdT / kf_sym[i])
    dRop_pdepdT = collect(dRop_pdepdT, Ctot_sym / T)
    write_eq(diff(Rop_sym[i], T), dRop_pdepdT)

    dkf_pdepde = diff(kf_pdep, extra_var)
    if not conp:
        # since the kf_pdep is expressed as a log
        # we need to solve for this in terms of dkf/de
        mul_term = __var_creator(kf_sym[i], extra_var)
        dkf_pdepde = dkf_pdepde * kf_sym[i]
        write_eq(diff(kf_pdep_sym[i], extra_var), dkf_pdepde)

    def get_dr_de(plog=True, writetofile=False, fwd=True):
        Ropt_sym = Ropf_sym if fwd else Ropr_sym
        Rop_temp = Ropf if fwd else Ropr
        nuv = nu_f if fwd else nu_r
        Sval = Sfwd if fwd else Srev
        if fwd:
            kt_sym = kf_pdep_sym if plog else kf_cheb_sym
        else:
            kt_sym = kr_pdep_sym if plog else kr_cheb_sym
        ksym = kf_sym if fwd else kr_sym

        # sub in Cns for proper temperature derivative
        Rop_temp = assert_subs(
            Rop_temp,
            (Product(Ck[k]**nuv[k, i], (k, 1, Ns)),
             Cns**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))),
            (ksym[i], kt_sym[i]),
            assumptions=[(ksym[i], kt_sym[i])])

        dRoptde = diff(Rop_temp, extra_var)
        if writetofile:
            write_eq(diff(Ropt_sym[i], extra_var), dRoptde)

        # sub in Ck[Ns]
        dRoptde = expand_mul(simplify(assert_subs(dRoptde, (Cns, Ck[Ns]))))

        # and go back original product
        dRoptde = assert_subs(
            dRoptde, (Ck[Ns] * Ck[Ns]**(nuv[Ns, i] - 1), Ck[Ns]**nuv[Ns, i]))
        dRoptde = assert_subs(dRoptde, (Ck[Ns]**nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
                                        Product(Ck[k]**nuv[k, i], (k, 1, Ns))))
        # and sub in C
        dRoptde = assert_subs(dRoptde, (Ctot, Ctot_sym))

        if writetofile:
            write_eq(diff(Ropt_sym[i], extra_var), dRoptde)

        # finally sub in the S term
        # need to modify the inner function to use k as the sum variable
        inner = __inner_func(Ns, fwd=fwd)

        # make sure it's equivalent before we mess with it
        assert_subs(dRoptde,
                    (inner, Sval[Ns]))

        # switch the sum variable
        inner = assert_subs(inner,
                            (__mod_prod_sum(Ns, fwd=fwd),
                             Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1))))
        # and force a subsitution
        dRoptde = assert_subs(dRoptde,
                              (inner, Sval[Ns]),
                              assumptions=[(inner, Sval[Ns])])

        if fwd:
            if plog:
                dkde = dkf_pdepde
            else:
                dkde = dkf_chebde
        else:
            if plog:
                dkde = dkr_pdepde
            else:
                dkde = dkr_chebde

        if not conp:
            # put the ROP back in
            dRoptde = assert_subs(dRoptde, (
                Ck[Ns] ** (nuv[Ns, i] + 1) / Ck[Ns], Ck[Ns] ** nuv[Ns, i]),
                (Ck[Ns] ** nuv[Ns, i] * Product(Ck[k]**nuv[k, i], (k, 1, Ns - 1)),
                    Product(Ck[k]**nuv[k, i], (k, 1, Ns))))

        dRoptde = assert_subs(dRoptde, (diff(kt_sym[i], extra_var), dkde),
                              (kt_sym[i], ksym[i]),
                              (Ropf if fwd else Ropr, Ropt_sym[i]),
                              assumptions=[(diff(kt_sym[i], extra_var), dkde),
                                           (kt_sym[i], ksym[i])])
        write_eq(diff(Ropt_sym[i], extra_var), dRoptde,
                 register=writetofile, sympy=writetofile)

        return dRoptde

    def get_dkr_de(dkfdeval, writetofile=True, plog=True):
        # find dkr/dT
        kft_sym = kf_pdep_sym if plog else kf_cheb_sym
        krt_sym = kr_pdep_sym if plog else kr_cheb_sym
        dkrde = diff(kft_sym[i] / Kc_sym[i], extra_var)
        if writetofile:
            write_eq(diff(krt_sym[i], extra_var), dkrde)
        dkrde = assert_subs(dkrde, (diff(kft_sym[i], extra_var), dkfdeval),
                            assumptions=[(diff(kft_sym[i], extra_var), dkfdeval)])
        # find the kf in the dkfdeval
        dkrde = assert_subs(dkrde,
                            (kf_sym[i], kft_sym[i]),
                            (kft_sym[i] / Kc_sym[i], krt_sym[i]),
                            (krt_sym[i], kr_sym[i]),
                            (Ropr_sym[i], Ropr),
                            assumptions=[
                                (kf_sym[i], kft_sym[i]),
                                (kft_sym[i] / Kc_sym[i], krt_sym[i]),
                                (krt_sym[i], kr_sym[i])])
        if plog:
            dkrde = factor_terms(dkrde)

        write_eq(diff(krt_sym[i], extra_var), dkrde)
        return dkrde

    # assemble the Rop derivatives
    if not conp:
        dRopf_pdepde = get_dr_de(plog=True, writetofile=False)
        dkr_pdepde = get_dkr_de(dkf_pdepde)
        dRopr_pdepde = get_dr_de(plog=True, writetofile=False, fwd=False)
        dRop_pdepde = dRopf_pdepde - dRopr_pdepde
        # do the same trick as for plog, where we sub out for a temporary
        # variable
        dRop_pdepde = __complex_collect(dRop_pdepde, dkf_pdepde / kf_sym[i])
        dRop_pdepde = collect(dRop_pdepde, 1 / (R * T))
        write_eq(diff(Rop_sym[i], extra_var), dRop_pdepde)

    else:
        dRopf_pdepde = dRopfdE
        dRopr_pdepde = dRoprdE
        dRop_pdepde = dRopf_pdepde - dRopr_pdepde

    latexfile.write('For Chebyshev reactions\n')
    mul_term = diff(kf_sym[i], T) / diff(log(kf_sym[i], 10), T)
    assert mul_term == kf_sym[i] * log(10)
    dkf_chebdT = diff(kf_cheb, T) * mul_term
    write_eq(diff(kf_sym[i], T), dkf_chebdT)
    dkf_chebdT = assert_subs(dkf_chebdT, (diff(Tred_sym, T), diff(Tred, T)))
    write_eq(diff(kf_sym[i], T), dkf_chebdT)

    # assemble the Rop derivatives
    dRopf_chebdT = get_dr_dt(cheb=True, writetofile=False)
    dkr_chebdT = get_dkr_dT(dkf_chebdT, writetofile=False, plog=False)
    dRopr_chebdT = get_dr_dt(cheb=True, fwd=False, writetofile=False)
    dRop_chebdT = dRopf_chebdT - dRopr_chebdT
    # do the same trick as for plog, where we sub out for a temporary variable
    dRop_chebdT = __complex_collect(dRop_chebdT, dkf_chebdT / kf_sym[i])
    dRop_chebdT = collect(dRop_chebdT, Ctot_sym / T)
    write_eq(diff(Rop_sym[i], T), dRop_chebdT)

    mul_term = diff(kf_cheb_sym[i], extra_var) / diff(
        log(kf_cheb_sym[i], 10), extra_var)
    dkf_chebde = diff(kf_cheb, extra_var) * mul_term
    if not conp:
        assert mul_term == kf_cheb_sym[i] * log(10)
        write_eq(diff(kf_cheb_sym[i], extra_var), dkf_chebde)
        register_equal(diff(Pred_sym, extra_var), diff(Pred, extra_var))
        dkf_chebde = assert_subs(
            dkf_chebde,
            (diff(Pred_sym, extra_var), diff(Pred, extra_var)))
        write_eq(diff(kf_cheb_sym[i], extra_var), dkf_chebde)
        dRopf_chebde = get_dr_de(plog=False, writetofile=False)
        dkr_chebde = get_dkr_de(dkf_chebde, plog=False, writetofile=False)
        dRopr_chebde = get_dr_de(plog=False, writetofile=False, fwd=False)
        dRop_chebde = dRopf_chebde - dRopr_chebde
        dRop_chebde = __complex_collect(dRop_chebde, dkf_chebde / kf_sym[i])
        dRop_chebde = collect(dRop_chebde, 1 / (R * T))
        write_eq(diff(Rop_sym[i], extra_var), dRop_chebde)

    else:
        dRopf_chebde = dRopfdE
        dRopr_chebde = dRoprdE
        dRop_chebde = dRopf_chebde - dRopr_chebde

    write_section('Jacobian entries')
    write_section('Energy Equation', sub=True)

    if conp:
        spec_heat = cp
        energy = h
    else:
        spec_heat = cv
        energy = u

    register_equal(diff(energy[k], T), spec_heat[k])

    # this will be used many times
    CkCpSum = Sum(Ck[k] * spec_heat[k], (k, 1, Ns))

    # save a copy of this form as it's very compact
    dTdt_simple = dTdt
    write_eq(dTdt_sym, dTdt, register=True)

    # and simplify the full sum more
    dTdt = assert_subs(
        dTdt, (CkCpSum, Sum(Ck[k] * spec_heat[k], (k, 1, Ns - 1)) +
               Cns * spec_heat[Ns]))
    write_eq(dTdt_sym, dTdt)

    num, den = fraction(dTdt)
    den = assert_subs(simplify(den), (Ctot, Ctot_sym))

    dTdt = num / den
    CkCpSum_full = den
    register_equal(CkCpSum_full, CkCpSum)
    write_eq(dTdt_sym, dTdt, register=True)

    write_section(r'\texorpdfstring{$\dot{T}$}{dTdt} Derivatives', sub=True)
    latexfile.write('Molar derivative\n')
    # Temperature jacobian entries
    register_equal(dTdt_simple, dTdt_sym)
    # first we do the concentration derivative
    dTdotdnj_sym = symbols(r'\frac{\partial\dot{T}}{\partial{n_j}}')

    # put in moles
    dTdotdnj = simplify(diff(
        assert_subs(dTdt, (Ck[k], nk[k] / V)),
        nk[j]))

    # put concentrations back in
    dTdotdnj = assert_subs(dTdotdnj, (nk[k] / V, Ck[k]))
    write_eq(dTdotdnj_sym, dTdotdnj)

    # Compact the CkCpSum back to a more reasonble representation
    # for sanity
    def __powsimp(expr):
        assert len(expr.args) == 2 and isinstance(expr, Pow)
        expr, power = expr.args
        return simplify(expr)**power

    dTdotdnj_rep = 0
    for term in Add.make_args(dTdotdnj):
        num, den = fraction(term)
        if num.has(CkCpSum_full):
            num = factor_terms(
                assert_subs(simplify(num), (CkCpSum_full, CkCpSum)))
        if isinstance(den, Pow):
            den = assert_subs(__powsimp(den),
                              (CkCpSum_full, CkCpSum))
        else:
            den = assert_subs(simplify(den),
                              (CkCpSum_full, CkCpSum))
        dTdotdnj_rep = dTdotdnj_rep + num / den
    dTdotdnj = dTdotdnj_rep
    write_eq(dTdotdnj_sym, dTdotdnj)

    dTdotdnj = assert_subs(dTdotdnj, (
        Sum(KroneckerDelta(j, k), (k, 1, Ns - 1)), 1), (
        Sum(-KroneckerDelta(j, k) *
            (spec_heat[Ns] - spec_heat[k]) / V, (k, 1, Ns - 1)),
        -(spec_heat[Ns] - spec_heat[j]) / V))
    write_eq(dTdotdnj_sym, dTdotdnj)

    # now expand to replace with the dT/dt term
    num, den = fraction(factor_terms(dTdotdnj, CkCpSum))
    # need to move to fraction rather than 1 /
    num = assert_subs(num, (-dTdt_simple, -dTdt_sym))
    dTdotdnj = num / den
    write_eq(dTdotdnj_sym, dTdotdnj)

    latexfile.write('Temperature derivative\n')

    # up next the temperature derivative
    dTdotdT_sym = symbols(r'\frac{\partial\dot{T}}{\partial{T}}')
    # first we must sub in the actual form of C, as the temperature derivative
    # is non-zero
    starting = assert_subs(dTdt, (Ctot_sym, Ctot), (nk[k] / V, Ck[k]))
    write_eq(dTdt_sym, starting)
    dTdotdT = diff(starting, T)

    write_eq(dTdotdT_sym, dTdotdT)

    # first up, go back to Ctot_sym
    dTdotdT = assert_subs(dTdotdT, (Ctot, Ctot_sym))
    write_eq(dTdotdT_sym, dTdotdT)

    # and collapse the cp sum
    rv = 0
    for arg in Add.make_args(dTdotdT):
        num, den = fraction(arg)
        if isinstance(den, Pow):
            rv = rv + num / \
                assert_subs(__powsimp(den), (CkCpSum_full, CkCpSum))
        else:
            rv = rv + num / assert_subs(simplify(den), (CkCpSum_full, CkCpSum))
    dTdotdT = rv

    write_eq(dTdotdT_sym, dTdotdT)

    # now we factor out the Ck cp sum
    dTdotdT = factor_terms(dTdotdT)
    write_eq(dTdotdT_sym, dTdotdT)

    # and replace the dTdt term
    dTdotdT = assert_subs(dTdotdT, (dTdt_simple, dTdt_sym),
                          (-dTdt_simple, -dTdt_sym))

    write_eq(dTdotdT_sym, dTdotdT)

    # the next simplification is of the [C] terms
    num, den = fraction(dTdotdT)
    num = assert_subs(num, (Ctot_sym, Sum(Ck[k], (k, 1, Ns))))
    dTdotdT = num / den
    write_eq(dTdotdT_sym, dTdotdT)

    num = assert_subs(num, (Sum(Ck[k], (k, 1, Ns)), Sum(
        Ck[k], (k, Ns, Ns)) + Sum(Ck[k], (k, 1, Ns - 1))))
    num = __simplify_per_term(collect(num, dTdt_sym))

    num = assert_subs(num, ((-diff(spec_heat[Ns], T) + spec_heat[Ns] / T) * Sum(Ck[k], (k, Ns, Ns)),
                            Sum((-diff(spec_heat[k], T) + spec_heat[Ns] / T) * Ck[k], (k, Ns, Ns))))

    num = __simplify_per_term(num)
    # collect terms inside sums
    terms = list(Add.make_args(num))
    for ind, term in enumerate(terms):
        inner = Mul.make_args(term)
        inner = [x if not isinstance(x, Sum) else
                 Sum(collect(x.function, (wdot[k], diff(wdot[k], T))), *x.limits) for x in inner]
        terms[ind] = Mul(*inner)
    num = Add(*terms)

    dTdotdT = num / den
    assert_subs(dTdotdT, (diff(energy[Ns], T), spec_heat[Ns]),
                assumptions=[(diff(energy[Ns], T), spec_heat[Ns])])
    write_eq(dTdotdT_sym, dTdotdT)

    # and finally substitute the energy derivative
    dTdotdT = assert_subs(dTdotdT, (diff(energy[k], T), spec_heat[k]))
    write_eq(dTdotdT_sym, dTdotdT)

    latexfile.write('{} Derivative\n'.format(extra_var_name))

    starting = assert_subs(dTdt, (
        Ctot_sym, Ctot))
    dTdotdE = diff(starting, extra_var)
    dTdotdE = assert_subs(dTdotdE, (
        Ctot, Ctot_sym))
    # derivatives of Ck
    dTdotdE = assert_subs(dTdotdE, (
        diff(Ck[k], extra_var), dCkde))

    # put the CkCp sums back together
    dTdotdE = assert_subs(
        dTdotdE, (CkCpSum_full, CkCpSum))

    # and factor out the sum
    dTdotdE = factor_terms(dTdotdE, CkCpSum)

    # and put dTdt back in
    dTdotdE = assert_subs(
        dTdotdE, (-dTdt_simple, -dTdt_sym))

    dTdotdE_sym = symbols(
        r'\frac{{\partial\dot{{T}}}}{{\partial{{{0}}}}}'.format(
            str(extra_var)))
    write_eq(dTdotdE_sym, dTdotdE, register=True, sympy=True)

    write_section(
        r'\texorpdfstring{{$\dot{{{0}}}$}}{{d{0}dt}} Derivatives'.format(
            extra_var), sub=True)

    extra_var_dot = MyImplicitSymbol(
        r'\dot{{ {} }}'.format(extra_var), (T, nk, V if conp else P))

    latexfile.write('Temperature Derivative\n')

    # put a dummy symbol in there that is dependent on T to get the
    # correct derivative of dTdt
    diff_val = MyImplicitSymbol(r'\dot{T}', (T))
    working = assert_subs(
        dExdt,
        (Ctot_sym, Ctot),
        (dTdt_sym, diff_val),
        assumptions=[(dTdt_sym, diff_val)]
    )
    # and replace the dummy with the original
    dEdotdT = diff(working, T)
    dEdotdT = assert_subs(
        dEdotdT,
        (diff_val, dTdt_sym),
        (1 / Ctot, 1 / Ctot_sym),
        (1 / (Ctot) / T, 1 / Ctot_sym / T),
        assumptions=[(diff_val, dTdt_sym),
                     (1 / Ctot, 1 / Ctot_sym),
                     (1 / (Ctot) / T, 1 / Ctot_sym / T)]
    )

    if conp:
        dEdotdT = expand_mul(dEdotdT)

    withR, withoutR = __separate_on(dEdotdT, R if not conp else Wk[k])

    if conp:
        withR = collect(simplify(withR), wdot[k])
        withR = Mul(*[
            x if not isinstance(x, Sum) else
            Sum(collect(x.function, (wdot[k] / T)), x.limits)
            for x in Mul.make_args(withR)])
        withR = Mul(*[
            x if not isinstance(x, Sum) else
            Sum(collect(x.function, (1 - Wk[k] / Wk[Ns])), x.limits)
            for x in Mul.make_args(withR)])
        withoutR = __complex_collect(withoutR, V / T)
    else:
        # do some collapsing
        # factor some terms
        withoutR = factor_terms(withoutR)
        # and collapse the Wk sum
        withR = simplify(assert_subs(
            withR, (
                T *
                Sum((1 - Wk[k] / Wk[Ns]) * diff(wdot[k], T), (k, 1, Ns - 1)),
                Sum(T * (1 - Wk[k] / Wk[Ns]) * diff(wdot[k], T), (k, 1, Ns - 1)))
        ))
        withR = assert_subs(
            withR,
            (next(x for x in Mul.make_args(withR) if isinstance(x, Sum)),
             Sum((1 - Wk[k] / Wk[Ns]) *
                 (T * diff(wdot[k], T) + wdot[k]), (k, 1, Ns - 1))
             )
        )
    # finally put back together
    dEdotdT = Add(*[withR, withoutR])

    write_eq(diff(extra_var_dot, T), dEdotdT, register=True, sympy=True)

    latexfile.write('Molar Derivative\n')

    # put a dummy symbol in there that is dependent on T to get the
    # correct derivative of dTdt
    diff_val = MyImplicitSymbol(r'\dot{T}', (nk))
    working = assert_subs(
        dExdt,
        (dTdt_sym, diff_val),
        assumptions=[(dTdt_sym, diff_val)]
    )
    # and replace the dummy with the original
    dEdotdnj = diff(working, nk[j])

    write_eq(diff(extra_var_dot, nk[j]), dEdotdnj, register=True, sympy=True)

    latexfile.write('{} Derivative\n'.format(extra_var_name))

    # put a dummy symbol in there that is dependent on T to get the
    # correct derivative of dTdt
    diff_val = MyImplicitSymbol(r'\dot{T}', (extra_var))
    working = assert_subs(
        dExdt,
        (dTdt_sym, diff_val),
        assumptions=[(dTdt_sym, diff_val)]
    )
    # and replace the dummy with the original
    dEdotde = diff(working, extra_var)
    if not conp:
        dEdotde = collect(dEdotde, 1 / T)
    else:
        dEdotde = expand_mul(dEdotde)
        dEdotde = simplify(collect(dEdotde, 1 / Ctot_sym))

        withW, withoutW = __separate_on(dEdotde, Wk[k])
        withW = assert_subs(
            withW, (
                next(x for x in Mul.make_args(withW) if isinstance(x, Sum)),
                Sum((1 - Wk[k] / Wk[Ns]) * (V * diff(wdot[k], V) + wdot[k]),
                    (k, 1, Ns - 1))
            )
        )
        withoutW = collect(withoutW, 1 / T)
        dEdotde = Add(*[withW, withoutW])

    write_eq(diff(extra_var_dot, extra_var),
             dEdotde, register=True, sympy=True)

    write_section(
        r'\texorpdfstring{$\dot{n_k}$}{dnkdt} Derivatives', sub=True)

    # concentration Jacobian equations
    dndot = MyIndexedFunc(r'\dot{n}', (nk, T, P, V))
    write_eq(diff(dndot[k], nk[j]), diff(dnkdt, nk[j]))
    write_eq(diff(dndot[k], T), diff(dnkdt, T))
    write_eq(diff(dndot[k], extra_var), diff(dnkdt, extra_var))

    # get wdot diffs in terms of dnk's
    dwdotdnj = solve(
        Eq(diff(dndot[k], nk[j]), diff(dnkdt, nk[j])), diff(wdot[k], nk[j]))[0]
    register_equal(diff(wdot[k], nk[j]), dwdotdnj)
    dwdotdT = solve(Eq(diff(dndot[k], T), diff(dnkdt, T)), diff(wdot[k], T))[0]
    register_equal(diff(wdot[k], T), dwdotdT)
    dwdotdE = solve(Eq(diff(dndot[k], extra_var), diff(dnkdt, extra_var)), diff(
        wdot[k], extra_var))[0]
    register_equal(diff(wdot[k], extra_var), dwdotdE)

    write_section('Jacobian Update Form')
    write_section('Temperature Derivatives', sub=True)

    dnk_omega_dt = assert_subs(dnkdt,
                               (wdot[k], omega_sym_q_k))

    domegadT = diff(dnk_omega_dt, T)

    dTdotdT = assert_subs(dTdotdT, (diff(wdot[k], T), dwdotdT))
    dEdotdT = assert_subs(dEdotdT, (diff(wdot[k], T), dwdotdT))

    write_eq(Jac[1, 1], dTdotdT, sympy=True)
    write_eq(Jac[2, 1], dEdotdT, sympy=True)
    write_eq(Jac[k + 2, 1], domegadT, sympy=True)

    latexfile.write('Converting to update form:\n')
    domegadT_update = Mul(*[x if not isinstance(x, Sum) else x.function
                            for x in Mul.make_args(domegadT)])

    write_dummy_eq(latex(Jac[k + 2, 1]) + r'\pluseq ' +
                   latex(domegadT_update) + r'\text{\quad} k = 1, \ldots, N_{sp} - 1')

    dRopdT_temp = Symbol(r'\Theta_{\partial T, i}')

    dqdT = assert_subs(diff(q, T), (diff(Rop_sym[i], T), dRopdT_temp),
                       assumptions=[(diff(Rop_sym[i], T), dRopdT_temp)])

    write_section('Explicit reversible reactions', subsub=True)
    write_eq(diff(q_sym[i], T), dqdT, enum_conds=reversible_type.explicit)
    write_eq(dRopdT_temp, dRop_expdT, enum_conds=reversible_type.explicit)

    write_section('Non-explicit reversible reactions', subsub=True)
    write_eq(diff(q_sym[i], T), dqdT, enum_conds=[reversible_type.non_explicit,
                                                  reaction_type.elementary, reaction_type.thd, reaction_type.fall, reaction_type.chem])
    write_eq(dRopdT_temp, dRop_nonexpdT, enum_conds=[reversible_type.non_explicit,
                                                     reaction_type.elementary, reaction_type.thd, reaction_type.fall, reaction_type.chem])

    write_section('Pressure-dependent reactions', subsub=True)

    dqdT_pdep = assert_subs(dqdT,
                            (ci[i], ci_elem),
                            (diff(ci[i], T), diff(ci_elem, T)),
                            assumptions=[(ci[i], ci_elem),
                                         (diff(ci[i], T), diff(ci_elem, T))])
    write_eq(diff(q_sym[i], T), dqdT_pdep)

    latexfile.write('For PLog reactions:\n')
    write_eq(dRopdT_temp, dRop_pdepdT, enum_conds=[reaction_type.plog])
    latexfile.write('For Chebyshev reactions:\n')
    write_eq(dRopdT_temp, dRop_chebdT, enum_conds=[reaction_type.cheb])

    write_section('Pressure independent reactions', subsub=True)

    dqdT_ind = assert_subs(dqdT,
                           (ci[i], ci_elem),
                           (diff(ci[i], T), diff(ci_elem, T)),
                           assumptions=[(ci[i], ci_elem),
                                        (diff(ci[i], T), diff(ci_elem, T))])
    write_eq(diff(q_sym[i], T), dqdT_ind,
             enum_conds=[reaction_type.elementary])

    write_section('Third-body enhanced reactions', subsub=True)
    latexfile.write('For mixture as third-body:\n')
    dqdT_thd = assert_subs(dqdT,
                           (ci[i], ci_thd_sym),
                           (diff(ci[i], T), dci_thddT),
                           assumptions=[(ci[i], ci_thd_sym),
                                        (diff(ci[i], T), dci_thddT)])
    write_eq(diff(q_sym[i], T), dqdT_thd, enum_conds=[
             reaction_type.thd, thd_body_type.mix])

    latexfile.write('For species $m$ as third-body:\n')
    dqdT_spec_thd = assert_subs(dqdT,
                                (ci[i], ci_thd_species),
                                (diff(ci[i], T), dci_spec_dT),
                                (Ctot_sym -
                                 Sum(Ck[k], (k, 1, Ns - 1)), Ck[Ns]),
                                assumptions=[(ci[i], ci_thd_species),
                                             (diff(ci[i], T), dci_spec_dT)])
    write_eq(diff(q_sym[i], T), dqdT_spec_thd, enum_conds=[
             reaction_type.thd, thd_body_type.species])

    latexfile.write(
        'If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$ for all species j:\n')
    dqdT_unity_thd = assert_subs(dqdT,
                                 (ci[i], Ctot_sym),
                                 (diff(ci[i], T), dci_unity_dT),
                                 assumptions=[(ci[i], Ctot_sym),
                                              (diff(ci[i], T), dci_unity_dT)])
    dqdT_unity_thd = collect(dqdT_unity_thd, Ctot_sym)
    write_eq(diff(q_sym[i], T), dqdT_unity_thd, enum_conds=[
             reaction_type.thd, thd_body_type.unity])

    write_section(
        'Unimolecular\slash recombination fall-off reactions', subsub=True)

    dqdT_fall_thd = assert_subs(dqdT,
                                (diff(ci[i], T), dci_falldT),
                                assumptions=[(diff(ci[i], T), dci_falldT)])
    dqdT_fall_thd = collect(dqdT_fall_thd, [ci[i], Pri_sym / (Pri_sym + 1),
                                            Rop_sym[i]])

    write_eq(diff(q_sym[i], T), dqdT_fall_thd,
             enum_conds=[reaction_type.fall])

    write_section(r'Chemically-activated bimolecular reactions', subsub=True)
    dqdT_chem_thd = assert_subs(dqdT,
                                (diff(ci[i], T), dci_chemdT),
                                assumptions=[(diff(ci[i], T), dci_chemdT)])
    dqdT_chem_thd = collect(dqdT_chem_thd, [ci[i], 1 / (Pri_sym + 1),
                                            Rop_sym[i]])
    write_eq(diff(q_sym[i], T), dqdT_chem_thd)

    write_section(
        'Reduced Pressure Derivatives', subsub=True
    )

    latexfile.write('For mixture as third-body:\n')
    write_eq(dPri_dT_prifac_sym, dPri_mixdT_prifac, enum_conds=[
        thd_body_type.mix])
    write_eq(dPri_dT_noprifac_sym, dPri_mixdT_noprifac, enum_conds=[
        thd_body_type.species])

    latexfile.write('For species $m$ as third-body:\n')
    write_eq(dPri_dT_prifac_sym, dPri_specdT_prifac, enum_conds=[
        thd_body_type.species])
    write_eq(dPri_dT_noprifac_sym, dPri_specdT_noprifac, enum_conds=[
        thd_body_type.species])

    latexfile.write(
        'If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$ for all species j:\n')

    write_eq(dPri_dT_prifac_sym, dPri_unitydT_prifac, enum_conds=[
        thd_body_type.unity])
    write_eq(dPri_dT_noprifac_sym, dPri_unitydT_noprifac, enum_conds=[
        thd_body_type.unity])

    write_section('Falloff Blending Function Forms', subsub=True)

    latexfile.write('For Lindemann\n')
    write_eq(dFi_dT_fac_sym, dFi_linddT_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.lind])

    latexfile.write('For Troe\n')
    write_eq(dFi_dT_fac_sym, dFi_troedT_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.troe])

    latexfile.write('For SRI\n')
    write_eq(dFi_dT_fac_sym, dFi_sridT_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.sri])

    write_section('Molar Derivatives', sub=True)

    dTdotdnj = assert_subs(dTdotdnj, (diff(wdot[k], nk[j]), dwdotdnj))
    dEdotdnj = assert_subs(dEdotdnj, (diff(wdot[k], nk[j]), dwdotdnj))

    write_eq(Eq(Jac[1, j + 2], dTdotdnj_sym), dTdotdnj,
             sympy=True)
    write_eq(Eq(Jac[2, j + 2], diff(extra_var_dot, nk[j])), dEdotdnj,
             sympy=True)
    domegadnj = diff(dnk_omega_dt, nk[j])
    dnkdotdnj = __var_creator(Symbol(r'\dot{n_k}'), nk[j])
    write_eq(Eq(Jac[k + 2, j + 2], dnkdotdnj), domegadnj,
             sympy=True)

    latexfile.write('Converting to Jacobian Update form:\n')
    domegadnj_update = Mul(*[x if not isinstance(x, Sum) else x.function
                             for x in Mul.make_args(domegadnj)])
    write_dummy_eq(
        latex(Jac[k + 2, j + 2]) + r'\pluseq ' + latex(domegadnj_update))

    Vdqdnj = diff(q, nk[j])
    Vdqdnj = assert_subs(Vdqdnj,
                         (diff(Rop_sym[i], nk[j]), dRopdnj))
    Vdqdnj = __simplify_per_term(V * Vdqdnj)
    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj)

    write_section('Pressure-dependent reactions', subsub=True)

    Vdqdnj_pdep = assert_subs(Vdqdnj,
                              (ci[i], ci_elem),
                              (diff(ci[i], nk[j]), diff(ci_elem, nk[j])),
                              assumptions=[(ci[i], ci_elem),
                                           (diff(ci[i], nk[j]), diff(ci_elem, nk[j]))])
    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj_pdep, enum_conds=[
             reaction_type.plog, reaction_type.chem])

    write_section('Pressure independent reactions', subsub=True)

    Vdqdnj_ind = assert_subs(Vdqdnj,
                             (ci[i], ci_elem),
                             (diff(ci[i], nk[j]), diff(ci_elem, nk[j])),
                             assumptions=[(ci[i], ci_elem),
                                          (diff(ci[i], nk[j]), diff(ci_elem, nk[j]))])
    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj_ind,
             enum_conds=[reaction_type.elementary])

    write_section('Third-body enhanced reactions', subsub=True)

    latexfile.write(r'\textbf{For mixture as third-body}:' + '\n')
    Vdqdnj_thd = assert_subs(Vdqdnj,
                             (ci[i], ci_thd_sym),
                             (diff(ci[i], nk[j]), dci_thddnj),
                             assumptions=[(ci[i], ci_thd_sym),
                                          (diff(ci[i], nk[j]), dci_thddnj)]
                             )

    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj_thd,
             enum_conds=[reaction_type.thd, thd_body_type.mix])

    latexfile.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    Vdqdnj_thd_spec = assert_subs(Vdqdnj,
                                  (ci[i], ci_thd_species),
                                  (diff(ci[i], nk[j]), dci_spec_dnj),
                                  (Ctot_sym -
                                   Sum(Ck[k], (k, 1, Ns - 1)), Ck[Ns]),
                                  assumptions=[(ci[i], ci_thd_species),
                                               (diff(ci[i], nk[j]), dci_spec_dnj)]
                                  )

    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj_thd_spec,
             enum_conds=[reaction_type.thd, thd_body_type.species])

    latexfile.write(
        r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    Vdqdnj_thd_unity = assert_subs(Vdqdnj,
                                   (ci[i], Ctot_sym),
                                   (diff(ci[i], nk[j]), dci_unity_dnj),
                                   assumptions=[(ci[i], Ctot_sym),
                                                (diff(ci[i], nk[j]), dci_unity_dnj)]
                                   )

    write_eq(V * diff(q_sym[k], nk[j]), Vdqdnj_thd_unity,
             enum_conds=[reaction_type.thd, thd_body_type.unity])

    write_section('Falloff Reactions', subsub=True)
    latexfile.write(
        r'\textbf{Unimolecular\slash recombination fall-off reactions}:' + '\n')

    dci_falldnj = __complex_collect(
        dci_falldnj, k0_sym * dPri_dnj_fac_sym / (kinf_sym * (Pri_sym + 1)), expand=True)
    Vdqdnj_fall_thd = assert_subs(Vdqdnj,
                                  (diff(ci[i], nk[j]), dci_falldnj),
                                  assumptions=[(diff(ci[i], nk[j]), dci_falldnj)])
    Vdqdnj_fall_thd = collect(Vdqdnj_fall_thd, ci[i])
    write_eq(V * diff(q_sym[i], nk[j]), Vdqdnj_fall_thd)

    write_section('Chemically-activated bimolecular reactions', subsub=True)

    dci_chemdnj = __complex_collect(
        dci_chemdnj, k0_sym * dPri_dnj_fac_sym / (kinf_sym * (Pri_sym + 1)), expand=True)
    Vdqdnj_chem_thd = assert_subs(Vdqdnj,
                                  (diff(ci[i], nk[j]), dci_chemdnj),
                                  assumptions=[(diff(ci[i], nk[j]), dci_chemdnj)])
    Vdqdnj_chem_thd = collect(Vdqdnj_chem_thd, ci[i])
    write_eq(V * diff(q_sym[i], nk[j]), Vdqdnj_chem_thd)

    write_section('Reduced Pressure Derivatives', subsub=True)

    latexfile.write(r'\textbf{For mixture as third-body}:' + '\n')

    write_eq(dPri_dnj_fac_sym, dPri_mixdnj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.mix])

    latexfile.write(r'\textbf{For species $m$ as third-body}:' + '\n')

    write_eq(dPri_dnj_fac_sym, dPri_specdnj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.species])
    latexfile.write(
        r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')

    write_eq(dPri_dnj_fac_sym, dPri_unitydnj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.unity])

    write_section('Falloff Blending Function Forms', subsub=True)

    latexfile.write('For Lindemann\n')
    write_eq(dFi_dnj_fac_sym, dFi_linddnj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.lind])

    latexfile.write('For Troe\n')
    write_eq(dFi_dnj_fac_sym, dFi_troednj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.troe])

    latexfile.write('For SRI\n')
    write_eq(dFi_dnj_fac_sym, dFi_sridnj_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem, falloff_form.sri])

    write_section('{} Derivatives'.format(extra_var_name), sub=True)

    dTdotdE = assert_subs(dTdotdE, (diff(wdot[k], extra_var), dwdotdE))
    dEdotde = assert_subs(dEdotde, (diff(wdot[k], extra_var), dwdotdE))
    write_eq(Eq(Jac[1, 2], dTdotdE_sym), dTdotdE,
             sympy=True)
    write_eq(Eq(Jac[2, 2], diff(extra_var_dot, extra_var)), dEdotde,
             sympy=True)
    domegade = simplify(diff(dnk_omega_dt, extra_var))
    write_eq(Eq(Jac[k + 2, 2], __var_creator(Symbol(r'\dot{n_k}'), extra_var)), domegade,
             sympy=True)

    latexfile.write('Converting to Jacobian Update form:\n')
    domegade_update = Mul(*[x if not isinstance(x, Sum) else x.function
                            for x in Mul.make_args(domegade)])
    write_dummy_eq(latex(Jac[k + 2, 2]) + r'\pluseq ' + latex(domegade_update))

    dqde = diff(q, extra_var)
    dqde = assert_subs(dqde,
                       (diff(Rop_sym[i], extra_var), dRopdE),
                       assumptions=[(diff(Rop_sym[i], extra_var), dRopdE)])
    write_eq(diff(q_sym[k], extra_var), dqde)

    write_section('Pressure-dependent reactions', subsub=True)

    latexfile.write('For PLOG:\n')
    dqde_plog = diff(q, extra_var)
    dqde_plog = assert_subs(dqde_plog,
                            (diff(Rop_sym[i], extra_var), dRop_pdepde),
                            assumptions=[(diff(Rop_sym[i], extra_var), dRop_pdepde)])

    dqde_plog = assert_subs(factor_terms(dqde_plog),
                            (ci[i], ci_elem),
                            (diff(ci[i], extra_var), diff(ci_elem, extra_var)),
                            assumptions=[(ci[i], ci_elem),
                                         (diff(ci[i], extra_var),
                                          diff(ci_elem, extra_var))])
    write_eq(diff(q_sym[k], extra_var), dqde_plog, enum_conds=[
             reaction_type.plog])

    latexfile.write('For Chebyshev:\n')
    dqde_cheb = diff(q, extra_var)
    dqde_cheb = assert_subs(dqde_cheb,
                            (diff(Rop_sym[i], extra_var), dRop_chebde),
                            assumptions=[(diff(Rop_sym[i], extra_var), dRop_chebde)])

    dqde_cheb = assert_subs(factor_terms(dqde_cheb),
                            (ci[i], ci_elem),
                            (diff(ci[i], extra_var), diff(ci_elem, extra_var)),
                            assumptions=[(ci[i], ci_elem),
                                         (diff(ci[i], extra_var),
                                          diff(ci_elem, extra_var))])
    write_eq(diff(q_sym[k], extra_var), dRop_chebde, enum_conds=[
             reaction_type.cheb])

    write_section('Pressure independent reactions', subsub=True)

    dqde_ind = assert_subs(dqde,
                           (ci[i], ci_elem),
                           (diff(ci[i], extra_var), diff(ci_elem, extra_var)),
                           assumptions=[(ci[i], ci_elem),
                                        (diff(ci[i], extra_var), diff(ci_elem, extra_var))])
    write_eq(diff(q_sym[k], extra_var), dqde_ind,
             enum_conds=[reaction_type.elementary])

    write_section('Third-body enhanced reactions', subsub=True)

    latexfile.write(r'\textbf{For mixture as third-body}:' + '\n')
    dqde_thd = assert_subs(dqde,
                           (ci[i], ci_thd_sym),
                           (diff(ci[i], extra_var), dci_thdde),
                           assumptions=[(ci[i], ci_thd_sym),
                                        (diff(ci[i], extra_var), dci_thdde)]
                           )

    write_eq(diff(q_sym[k], extra_var), dqde_thd,
             enum_conds=[reaction_type.thd, thd_body_type.mix])

    latexfile.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    dqde_thd_spec = assert_subs(dqde,
                                (ci[i], ci_thd_species),
                                (diff(ci[i], extra_var), dci_spec_de),
                                (Ctot_sym -
                                 Sum(Ck[k], (k, 1, Ns - 1)), Ck[Ns]),
                                assumptions=[(ci[i], ci_thd_species),
                                             (diff(ci[i], extra_var), dci_spec_de)]
                                )

    write_eq(diff(q_sym[k], extra_var), dqde_thd_spec,
             enum_conds=[reaction_type.thd, thd_body_type.species])

    latexfile.write(
        r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    dqde_thd_unity = assert_subs(dqde,
                                 (ci[i], Ctot_sym),
                                 (diff(ci[i], extra_var), dci_unity_de),
                                 assumptions=[(ci[i], Ctot_sym),
                                              (diff(ci[i], extra_var), dci_unity_de)]
                                 )

    write_eq(diff(q_sym[k], extra_var), dqde_thd_unity,
             enum_conds=[reaction_type.thd, thd_body_type.unity])

    write_section(
        r'Unimolecular/recombination fall-off reactions', subsub=True)
    dqde_fall_thd = assert_subs(dqde,
                                (diff(ci[i], extra_var), dci_fallde),
                                assumptions=[(diff(ci[i], extra_var), dci_fallde)])
    dqde_fall_thd = collect(dqde_fall_thd, ci[i])
    write_eq(diff(q_sym[i], extra_var), dqde_fall_thd)

    write_section(r'Chemically-activated bimolecular reactions', subsub=True)
    dqde_chem_thd = assert_subs(dqde,
                                (diff(ci[i], extra_var), dci_chemde),
                                assumptions=[(diff(ci[i], extra_var), dci_chemde)])
    dqde_chem_thd = collect(dqde_chem_thd, ci[i])
    write_eq(diff(q_sym[i], extra_var), dqde_chem_thd)

    write_section(r'Reduced Pressure Derivatives', subsub=True)
    latexfile.write(r'\textbf{For mixture as third-body}:' + '\n')
    write_eq(dPri_de_prifac_sym, dPri_mixde_prifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.mix])

    write_eq(dPri_de_noprifac_sym, dPri_mixde_noprifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.mix])

    latexfile.write(r'\textbf{For species $m$ as third-body}:' + '\n')
    write_eq(dPri_de_prifac_sym, dPri_specde_prifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.species])

    write_eq(dPri_de_noprifac_sym, dPri_specde_noprifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.species])

    latexfile.write(
        r'\textbf{If all $' + latex(thd_bdy_eff[j, i]) + ' = 1$}:' + '\n')
    write_eq(dPri_de_prifac_sym, dPri_unityde_prifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.unity])

    write_eq(dPri_de_noprifac_sym, dPri_unityde_noprifac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         thd_body_type.unity])

    write_section('Falloff Blending Function Forms', subsub=True)

    latexfile.write('For Lindemann\n')
    write_eq(dFi_de_fac_sym, dFi_lindde_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.lind])

    latexfile.write('For Troe\n')
    write_eq(dFi_de_fac_sym, dFi_troede_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.troe])

    latexfile.write('For SRI\n')
    write_eq(dFi_de_fac_sym, dFi_sride_fac,
             enum_conds=[reaction_type.fall, reaction_type.chem,
                         falloff_form.sri])


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

    def close(self):
        self.write(r'\end{document}' + '\n')
        self.lines = [self.regex.sub(r'{dmath} ', line) for line in self.lines]
        with open(self.name, self.mode) as file:
            file.writelines(self.lines)

    def __exit__(self, type, value, traceback):
        self.close()


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

    def close(self):
        variables = set()
        for var, eqn in self.equations.items():
            if isinstance(eqn, list):
                variables = variables.union(set([var]))
                for e, dummy in eqn:
                    variables = variables.union(e.free_symbols)
            else:
                variables = variables.union(set([var]).union(eqn.free_symbols))

        # write equations
        with open(os.path.join(home_dir, self.name), self.mode) as file:
            # write variables (for easier searching)
            for var in variables:
                file.write(srepr(var) + '\n')

            file.write('\n')

            for var, eqn in self.equations.items():
                file.write(srepr(var) + '\n')
                if isinstance(eqn, list):
                    for e, conditions in eqn:
                        try:
                            conditions = iter(conditions)
                        except:
                            conditions = iter([conditions])
                        file.write(
                            'if {}\n{}\n'.format(','.join([srepr(c) for c in conditions]), srepr(e)))
                    file.write('\n')
                else:
                    file.write(srepr(eqn) + '\n\n')

    def __exit__(self, type, value, traceback):
        self.close()
