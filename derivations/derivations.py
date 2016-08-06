from sympy.interactive import init_printing
from sympy.simplify.radsimp import collect, fraction
from sympy.simplify.simplify import simplify
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
from sympy.core.function import UndefinedFunction, Function, diff, Derivative, expand
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.compatibility import is_sequence
from sympy.core.numbers import Rational
from constants import *

init_printing()

class CustomLatexPrinter(LatexPrinter):
    pass

#override default latex print method
def latex(expr, **settings):
    return CustomLatexPrinter(settings).doprint(expr)    


class FunctionalSymbol(Symbol):
    def __new__(cls, name, args, full_print=False, **assumptions):
        obj = Symbol.__new__(cls, name, **assumptions)
        obj.function_of = args
        obj.full_print = full_print
        return obj

    def __str__(self):
        return super(FunctionalSymbol, self).__str__() if not self.full_print else \
            self.function_of.__str__()

    def _get_iter_func(self):
        funcof = self.function_of
        if not hasattr(self.function_of, '__iter__'):
            funcof = [self.function_of]

        return funcof

    @property
    def free_symbols(self):
        return super(FunctionalSymbol, self).free_symbols.union(*[
            x.free_symbols for x in self._get_iter_func()])

    def _eval_diff(self, wrt, **kw_args):
            return self._eval_derivative(wrt)

    def _eval_derivative(self, wrt):
        if self == wrt:
            return S.One
        elif wrt == self.function_of:
            base_str_total = r'\frac{{\text{{d}} {} }}{{\text{{d}} {} }}'
            base_str_partial = r'\frac{{\partial {} }}{{\partial {} }}'
            funcof = self._get_iter_func()
            i = 0
            l = []
            base_str = base_str_total if len(funcof) == 1 else base_str_partial 
            for a in self._get_iter_func():
                i += 1
                da = a.diff(wrt)
                if da is S.Zero:
                    continue
                df = FunctionalSymbol(base_str.format(
                str(self.name), str(a)), args=self.function_of)
                
                l.append(df * da)
            return Add(*l)
        else:
            return S.Zero


class IndexedFunc(IndexedBase):
    def __new__(cls, label, args, shape=None, **kw_args):
        obj = IndexedBase.__new__(cls, label, shape=shape, **kw_args)
        obj.function_of = args
        return obj

    def _get_iter_func(self):
        funcof = self.function_of
        if not hasattr(self.function_of, '__iter__'):
            funcof = [self.function_of]

        return funcof

    @property
    def free_symbols(self):
        return super(IndexedBase, self).free_symbols.union(*[
            x.free_symbols for x in self._get_iter_func()])

    class IndexedFuncValue(Indexed):
        def __new__(cls, base, function_of, *args):
            obj = Indexed.__new__(cls, base, *args)
            obj.function_of = function_of
            return obj

        def _get_iter_func(self):
            funcof = self.function_of
            if not hasattr(self.function_of, '__iter__'):
                funcof = [self.function_of]

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
                elif self.function_of != wrt.function_of:
                    msg = "Different function form d({!s})/d({!s})".format(self.function_of,
                                                                        wrt.function_of)
                    raise IndexException(msg)
                result = S.One
                for index1, index2 in zip(self.indices, wrt.indices):
                    result *= KroneckerDelta(index1, index2)
                return result
            else:
                #f(x).diff(s) -> x.diff(s) * f.fdiff(1)(s)
                i = 0
                l = []
                base_str_total = r'\frac{{\text{{d}} {} }}{{\text{{d}} {} }}'
                base_str_partial = r'\frac{{\partial {} }}{{\partial {} }}'
                funcof = self._get_iter_func()
                base_str = base_str_total if len(funcof) == 1 else base_str_partial 
                for a in self._get_iter_func():
                    i += 1
                    da = a.diff(wrt)
                    if da is S.Zero:
                        continue
                    df = IndexedFunc(base_str.format(
                    str(self.base), str(a)), args=self.function_of)[self.args[1]]
                    
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
            return IndexedFunc.IndexedFuncValue(self, self.function_of,
                *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return IndexedFunc.IndexedFuncValue(self, self.function_of,
                indices, **kw_args)

"""
Actual derivation
"""

def write_eq(eq, simiplify=False):
    if simiplify:
        file.write(latex(simplify(eq), mode='equation') + '\n')
    else:
        file.write(latex(eq, mode='equation') + '\n')

def factor_and_solve(expr, factor):
    expr = collect(expand(expr), factor)
    fac_args = [i for i, arg in enumerate(expr.args) if arg.atoms(factor)]
    noFac_args = [i for i in range(len(expr.args)) if i not in fac_args]
    if len(fac_args) == 1:
        fac_args = expr.args[fac_args[0]]
    else:
        fac_args = Add(*[expr.args[i] for i in fac_args])
    if len(noFac_args) == 1:
        noFac_args = expr.args[noFac_args[0]]
    else:
        noFac_args = Add(*[expr.args[i] for i in noFac_args])
    return -noFac_args / (fac_args / factor)

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
    T = FunctionalSymbol('T', t)
    Wi = IndexedBase('W')
    Wtot = symbols(r'\bar{W}')

    #some constants, and state variables
    Patm = S.atm_pressure
    R = S.gas_constant
    m = S.mass

    Xi = IndexedFunc('X', t)

    #molecular weight and moles
    W = Sum(Xi[i] * Wi[i], (i, 1, Ns))
    write_eq(Eq(Wtot, W))
    n = m / W
    n_sym = Function('n')(t)
    write_eq(Eq(n_sym, n))

    #more thermo
    if conp:
        P = S.pressure
        P_sym = S.pressure
        V = n * R * T / P
        V_sym = FunctionalSymbol('V', t)
    else:
        V = S.volume
        V_sym = S.volume
        P = n * R * T / V
        P_sym = FunctionalSymbol('P', t)

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

    #first we define the system
    file.write(r'\begin{equation}\Phi = \left\{T, [X]_1, [X]_2, \ldots [X]_{N_{sp}}\right\}^{T}\end{equation}'
        + '\n')

    file.write(r'\begin{equation}\frac{\partial \Phi}{\partial t}' +
        r' = \left\{\frac{\partial T}{\partial t}' +
        r', \frac{\partial [X]_1}{\partial t}' +
        r', \frac{\partial [X]_2}{\partial t}' + 
        r', \ldots \frac{\partial [X]_{N_{sp}}}{\partial t}\right\}^{T}\end{equation}'
        + '\n')

    Xtot = symbols(r'[X]')
    Xtot_eq = Eq(Xtot, P / (R * T))
    write_eq(Xtot_eq)
    Xtot = solve(Xtot_eq, Xtot)[0]
    #solve for C_ns
    Xns = Xtot - Sum(Xi, (i, 1, Ns - 1))
    write_eq(Eq(Xi[Ns], Xns))


    #now define our time derivatives
    U = n * Sum(Xi[i] * hi[i], (i, 1, Ns)) - P * V
    U_sym = Function('U')(t)

    energy_conv = Eq(diff(U_sym, t), -P_sym * diff(V_sym, t))
    write_eq(energy_conv)

    if conp:
        H_sym = Function('H')(t)
        Heq = U + P * V
        write_eq(Eq(H_sym, Heq))

        enthalpy_diff = Eq(diff(H_sym), diff(U_sym + P_sym * V_sym, t))
        write_eq(enthalpy_diff)
        du_dt = solve(enthalpy_diff, diff(U_sym, t))[0]
        write_eq(Eq(diff(U_sym, t), du_dt))
        energy_conv = Eq(diff(H_sym, t),
            solve(energy_conv.subs(diff(U_sym, t), du_dt), diff(H_sym, t))[0])
        write_eq(energy_conv)

        #we now have dH/dt = 0
        #so let's get that as a function of temperature
        energy_conv = diff(Heq, t)
        write_eq(Eq(energy_conv, 0))
        #due to sympy's inability to solve sums, we have to do this one manually
        dTdt = simplify(factor_and_solve(energy_conv, diff(T, t)))
        num, den = fraction(dTdt)
        dTdt = num / simplify(den)
        write_eq(Eq(diff(T, t), dTdt))
        
    else:
        energy_conv = simplify(energy_conv.subs(U_sym, U).subs(P_sym, P))

    #Temperature jacobian entries
    dTdtdx = symbols(r'\frac{\partial\dot{T}}{\partial{X_j}}')
    write_eq(Eq(dTdtdx, simplify(diff(dTdt, Xi[j]))))
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
    rop = kf_sym[j] * SmartProduct(Xi[i]**nu_f[i, j], (i, 1, Ns)) - kr_sym * SmartProduct(Xi[i]**nu_r[i, j], (i, 1, Ns))
    rop_sym = IndexedFunc(r'{R_{net}}', args=(Xi, T, nu))

    write_eq(Eq(rop_sym[j], rop))
    
    #net reaction rate
    omega = Sum(rop, (j, 1, Nr))
    write_eq(Eq(diff(Xi[i], t), omega))

    #concentration Jacobian equations
    dXdot = IndexedFunc(r'\dot{X}', (Xi[k], T))
    write_eq(Eq(diff(dXdot[i], Xi[j]), simplify(diff(omega, Xi[k]))))
    write_eq(Eq(diff(dXdot[i], T), simplify(diff(omega, T))))


if __name__ == '__main__':
    with open('derivations/derivs.tex', 'w') as file:
        file.write(r'\documentclass[a4paper,10pt]{article}' + '\n' +
                   r'\usepackage[utf8]{inputenc}' + '\n'
                   r'\usepackage{amsmath}' + '\n')
        file.write(r'\begin{document}' + '\n') 
        derivation(file)
        file.write(r'\end{document}' + '\n') 