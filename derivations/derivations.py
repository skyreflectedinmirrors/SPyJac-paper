from sympy.interactive import init_printing
from sympy.simplify.radsimp import collect, fraction
from sympy.simplify.simplify import simplify, cancel, separatevars
from sympy.solvers.solvers import solve
from sympy.core.symbol import symbols, Symbol
from sympy.core.relational import Eq
from sympy.core.sympify import sympify
from sympy.core.mul import Mul
from sympy.core.add import Add
from sympy.tensor.indexed import Idx, IndexedBase, Indexed
from sympy.core.symbol import Symbol
from sympy.concrete import Sum, Product
from sympy.printing.latex import LatexPrinter
from sympy.core.function import UndefinedFunction, Function, diff, Derivative, expand, expand_mul
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.compatibility import is_sequence
from sympy.core.numbers import Rational
from sympy.core.exprtools import factor_terms
from sympy.core.relational import Equality
from constants import *

init_printing()

class CustomLatexPrinter(LatexPrinter):
    pass

#override default latex print method
def latex(expr, **settings):
    return CustomLatexPrinter(settings).doprint(expr)

base_str_total = r'\frac{{\text{{d}} {} }}{{\text{{d}} {} }}'
base_str_partial = r'\frac{{\partial {} }}{{\partial {} }}'
class SymbolicFunction(Function):
    def __new__(cls, name, *args, **options):
        full_print = False
        functional_form = args[0]
        if 'full_print' in options:
            full_print = options['full_print']
            del options['full_print']

        obj = Function.__new__(cls, name, *args, **options)
        obj.functional_form = functional_form
        obj.full_print = full_print
        return obj

    def symbol(self):
        return self.args[0]

    def _eval_subs(self, old, new):
        if self == old:
            return new
        if self.functional_form.has(old):
            return SymbolicFunction(str(self), \
            self.functional_form.subs(old, new))
        return new

    @property
    def free_symbols(self):
        return super(SymbolicFunction, self).free_symbols.union(
            self.functional_form.free_symbols)

    def __str__(self):
        if not self.full_print:
            return self.args[0].__str__()
        else:
            return self.functional_form.__str__()

    def _latex(self, *args, **kwargs):
        return self.__str__()

    def _eval_diff(self, wrt, **kw_args):
            return self._eval_derivative(wrt)

    def _eval_derivative(self, wrt):
        if self == wrt:
            return S.One
        else:

            funcof = self.functional_form.free_symbols
            i = 0
            l = []
            base_str = base_str_total if len(funcof) == 1 else base_str_partial
            da = self.functional_form.diff(wrt)
            if da is S.Zero:
                return S.Zero
            return SymbolicFunction(Symbol(base_str.format(
                str(self.args[0]), str(wrt))), da,
            full_print=self.full_print)

class ImplicitSymbol(Symbol):
    def __new__(cls, name, args, **assumptions):
        obj = Symbol.__new__(cls, name, **assumptions)
        obj.functional_form = args
        return obj

    def _get_iter_func(self):
        funcof = self.functional_form
        if not funcof:
            return []
        if not hasattr(self.functional_form, '__iter__'):
            funcof = [self.functional_form]

        return funcof

    def _eval_subs(self, old, new):
        if old == self:
            return new
        if self.functional_form.has(old):
            return ImplicitSymbol(str(self),
                self.functional_form.subs(old, new))
        return self

    @property
    def free_symbols(self):
        return super(ImplicitSymbol, self).free_symbols.union(*[
            x.free_symbols for x in self._get_iter_func()])

    def _eval_diff(self, wrt, **kw_args):
            return self._eval_derivative(wrt)

    def _eval_derivative(self, wrt):
        if self == wrt:
            return S.One
        else:
            funcof = self._get_iter_func()
            i = 0
            l = []
            base_str = base_str_total if len(funcof) == 1 else base_str_partial 
            for a in self._get_iter_func():
                i += 1
                da = a.diff(wrt)
                if da is S.Zero:
                    continue
                df = ImplicitSymbol(base_str.format(
                str(self.name), str(wrt)), args=self.functional_form)
                
                l.append(df * da)
            return Add(*l)

class IndexedFunc(IndexedBase):
    def __new__(cls, label, args, shape=None, **kw_args):
        obj = IndexedBase.__new__(cls, label, shape=shape, **kw_args)
        obj.functional_form = args
        return obj

    def _eval_simplify(self, ratio=1.7, measure=None):
        return IndexedFunc(self.label,
            *[simplify(x, ratio=ratio, measure=measure)
                         for x in self.args])

    def _get_iter_func(self):
        funcof = self.functional_form
        if not hasattr(self.functional_form, '__iter__'):
            funcof = [self.functional_form]

        return funcof

    @property
    def free_symbols(self):
        return super(IndexedBase, self).free_symbols.union(*[
            x.free_symbols for x in self._get_iter_func()])

    class IndexedFuncValue(Indexed):
        def __new__(cls, base, functional_form, *args):
            obj = Indexed.__new__(cls, base, *args)
            obj.functional_form = functional_form
            return obj

        def _eval_simplify(self, ratio=1.7, measure=None):
            return IndexedFunc.IndexedFuncValue(
                        self.base,
                        *[simplify(x, ratio=ratio, measure=measure)
                                 for x in self.args])


        def _eval_subs(self, old, new):
            if self == old:
                return new
            if self.functional_form.has(old):
                return IndexedFunc.IndexedFuncValue(self.base, 
                self.functional_form.subs(old, new),
                *self.indices)
            return new

        def _get_iter_func(self):
            funcof = self.functional_form
            if not hasattr(self.functional_form, '__iter__'):
                funcof = [self.functional_form]

            return funcof
        def _eval_diff(self, wrt, **kw_args):
            return self._eval_derivative(wrt)
        def _eval_derivative(self, wrt):
            if self == wrt:
                return S.One
            elif isinstance(wrt, IndexedFunc.IndexedFuncValue) and wrt.base == self.base:
                if len(self.indices) != len(wrt.indices):
                    msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                           wrt)
                    raise IndexException(msg)
                elif self.functional_form != wrt.functional_form:
                    msg = "Different function form d({!s})/d({!s})".format(self.functional_form,
                                                                        wrt.functional_form)
                    raise IndexException(msg)
                result = S.One
                for index1, index2 in zip(self.indices, wrt.indices):
                    result *= KroneckerDelta(index1, index2)
                return result
            else:
                #f(x).diff(s) -> x.diff(s) * f.fdiff(1)(s)
                i = 0
                l = []
                funcof = self._get_iter_func()
                base_str = base_str_total if len(funcof) == 1 else base_str_partial 
                for a in self._get_iter_func():
                    i += 1
                    da = a.diff(wrt)
                    if da is S.Zero:
                        continue
                    df = IndexedFunc(base_str.format(
                    str(self.base), str(wrt)), args=self.functional_form)[self.args[1]]
                    
                    l.append(df * da)
                return Add(*l)

        @property
        def free_symbols(self):
            return super(Indexed, self).free_symbols.union(*[
            x.free_symbols for x in self._get_iter_func()])

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
            if self.shape and len(self.shape) != len(indices):
                raise IndexException("Rank mismatch.")
            return IndexedFunc.IndexedFuncValue(self.label,
                self.functional_form,
                *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return IndexedFunc.IndexedFuncValue(self.label,
                self.functional_form,
                indices, **kw_args)

"""
Actual derivation
"""

def write_eq(eq):
    if isinstance(eq, SymbolicFunction) or \
       isinstance(eq, IndexedFunc.IndexedFuncValue) or \
       isinstance(eq, ImplicitSymbol):
        file.write(latex(Eq(eq, eq.functional_form), mode='equation') + '\n')
    else:
        file.write(latex(eq, mode='equation') + '\n')

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
            out_args.append(Add(*[sum_simplifier(x) for x in arg.args]))
        else:
            out_args.append(simplify(arg))
    return Mul(*out_args)

def functional_simplfier(expr):
    return expr.subs([(x, x.functional_form) for x in expr.atoms(SymbolicFunction)])

def derivation(file, conp = True):
    #mechanism size
    Ns = S.Ns
    Nr = S.Nr

    #index variables
    i = Idx('i', Ns + 1)
    j = Idx('j', Nr + 1)
    k = Idx('k')

    #time
    t = symbols('t', float=True, finite=True, negative=False, real=True)


    class SmartProduct(Product):
        def _eval_diff(self, x, **kw_args):
                return self._eval_derivative(x)
        def _eval_derivative(self, x, **kw_args):
            """
            Differentiate wrt x as long as x is not in the free symbols of any of
            the upper or lower limits.
            Prod(a*b*x, (x, 1, a)) can be differentiated wrt x or b but not `a`
            since the value of the sum is discontinuous in `a`. In a case
            involving a limit variable, the unevaluated derivative is returned.
            """

            # diff already confirmed that x is in the free symbols of self, but we
            # don't want to differentiate wrt any free symbol in the upper or lower
            # limits
            # XXX remove this test for free_symbols when the default _eval_derivative is in
            if x.is_Indexed:
                from sympy import IndexedBase
                if x.base not in self.atoms(IndexedBase):
                    return S.Zero
            elif x not in self.free_symbols:
                return S.Zero

            # get limits and the function
            f, limits = self.function, list(self.limits)

            limit = limits.pop(-1)

            if limits:  # f is the argument to a Sum
                f = self.func(f, *limits)

            if len(limit) == 3:
                _, a, b = limit
                if x in a.free_symbols or x in b.free_symbols:
                    return None
                df = Derivative(f, x, evaluate=True)
                rv = self.func(df, limit)
                if limit[0] not in df.free_symbols:
                    rv = rv.doit()
                return rv
            else:
                return NotImplementedError('Lower and upper bound expected.')

    #thermo vars
    T = ImplicitSymbol('T', t)
    Ci = IndexedFunc('[C]', t)
    Wi = IndexedBase('W')

    #some constants, and state variables
    Patm = S.atm_pressure
    R = S.gas_constant
    m = S.mass

    #define concentration
    if conp:
        P = S.pressure
        V = ImplicitSymbol('V', t)
        state_vec = [T, Ci[1], Ci[2], Ci[Ns - 1]]
    else:
        V = S.volume
        P = SymbolicFunction('P', t)
        state_vec = [T, Ci[1], Ci[2], Ci[Ns - 1]]

    #define state vector
    state_vec_str = ' = ' + r'\left\{{{}\ldots {}\right\}}'
    state = ImplicitSymbol(r'\Phi', t)
    write_dummy_eq(str(state) + state_vec_str.format(
        ','.join([str(x) for x in state_vec[:-1]]),
        str(state_vec[-1])))

    write_dummy_eq(str(diff(state, t)) + state_vec_str.format(
        ','.join([str(diff(x, t)) for x in state_vec[:-1]]),
        str(diff(state_vec[-1], t))))

    n = SymbolicFunction('n', P * V / (R * T))
    write_eq(n)

    Ctot = SymbolicFunction(Symbol('[C]'), P / (R * T))
    write_eq(Ctot)
    Cns = SymbolicFunction(Symbol('[C]_{N_s}'), Ctot - Sum(Ci[i], (i, 1 , Ns - 1)))
    write_eq(Cns)

    Xi = IndexedFunc('X', Ci / Ctot)
    Xns = Cns / Ctot

    #molecular weight
    W = factor_terms(Sum(Wi[i] * Xi[i], (i, 1, Ns - 1)) + Wi[Ns] * Xns,
        1 / Ctot)
    W = SymbolicFunction('W', W)
    write_eq(W)

    #polyfits
    a = IndexedBase('a')

    cp = R * (a[i, 0] + T * (a[i, 1] + T * (a[i, 2] + T * (a[i, 3] + a[i, 4] * T))))
    cpi = IndexedFunc('{c_p}', T)

    write_eq(Eq(cpi[i], cp))
    write_eq(Eq(diff(cpi[i], T), simplify(diff(cp, T))))

    h = R * T * (a[i, 0] + T * (a[i, 1] * Rational(1, 2) + T * (a[i, 2] * Rational(1, 3) + T * (a[i, 3] * Rational(1, 4) + a[i, 4] * T * Rational(1, 5)))))
    hi = IndexedFunc('h', T)
    write_eq(Eq(hi[i], h))
    write_eq(Eq(diff(hi[i], T), simplify(diff(h, T))))

    B = a[i, 6] - a[i, 0] + (a[i, 0] - 1) * log(T) + T * (a[i, 1] * Rational(1, 2) + T * (a[i, 2] * Rational(1, 6)  + T * (a[i, 3] * Rational(1, 12)  + a[i, 4] * T * Rational(1, 20)))) - a[i, 5] / T 
    B_sym = IndexedFunc(r'B', T)

    write_eq(Eq(B_sym[i], B))
    write_eq(Eq(diff(B_sym[i], T), simplify(diff(B, T))))

    U = ImplicitSymbol('U', t)
    dUdt = diff(U, t)
    dUdt.functional_form = -P * diff(V, t)
    write_eq(dUdt)

    if conp:
        H = SymbolicFunction('H', U + P * V)
        dHdt = diff(H, t)
        write_eq(dHdt)
        dHdt.functional_form = dHdt.functional_form.subs(dUdt, -P * diff(V, t))
        write_eq(dHdt)
        #start from dH/dt = 0
        H.functional_form = V * (Sum(Ci[i] * hi[i], (i, 1, Ns - 1)) + Cns * hi[Ns])
        write_eq(H)

        H = H.subs(Cns, Cns.functional_form)
        write_eq(H)

        return
    else:
        raise NotImplementedError


    #Temperature jacobian entries
    dTdtdx = symbols(r'\frac{\partial\dot{T}}{\partial{C_j}}')
    write_eq(Eq(dTdtdx, simplify(diff(dTdt, Ci[j]))))
    dTdtdT = symbols(r'\frac{\partial\dot{T}}{\partial{T}}')
    write_eq(Eq(dTdtdT, simplify(diff(dTdt, T))))

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
    write_eq(Eq(diff(Ci[i], t), omega))

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
    derivation(file)
    finalize()
    