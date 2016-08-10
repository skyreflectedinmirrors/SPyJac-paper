from sympy.core.symbol import Symbol
from sympy.tensor.indexed import Idx, IndexedBase, Indexed
from sympy.concrete import Product
from sympy.core.compatibility import is_sequence
from sympy.core.singleton import S
from sympy.core.add import Add
from sympy.core.function import Derivative
from sympy.functions.special.tensor_functions import KroneckerDelta

base_str_total = r'\frac{{\text{{d}} {} }}{{\text{{d}} {} }}'
base_str_partial = r'\frac{{\partial {} }}{{\partial {} }}'

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
            for a in funcof:
                i += 1
                da = a.diff(wrt)
                if da is S.Zero:
                    continue
                df = ImplicitSymbol(base_str.format(
                str(self.name), str(a)), args=self.functional_form)
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
                         for x in self._get_iter_func()])

    def _get_iter_func(self):
        funcof = self.functional_form
        if not hasattr(self.functional_form, '__iter__'):
            funcof = [self.functional_form]

        return funcof

    @property
    def free_symbols(self):
        return set([self]).union(*[
            x.free_symbols for x in self._get_iter_func()])

    class IndexedFuncValue(Indexed):
        def __new__(cls, base, *args):
            functional_form = args[0]
            obj = Indexed.__new__(cls, base, *args)
            obj.functional_form = functional_form
            return obj

        @property
        def indices(self):
            return self.args[2:]

        def _eval_simplify(self, ratio=1.7, measure=None):
            return IndexedFunc.IndexedFuncValue(
                        self.base,
                        *[simplify(x, ratio=ratio, measure=measure)
                                 for x in self._get_iter_func()])

        def _eval_subs(self, old, new):
            if self == old:
                return new
            if any(x.has(old) for x in self._get_iter_func()):
                return IndexedFunc.IndexedFuncValue(self.base, 
                tuple(x.subs(old, new) for x in self._get_iter_func()),
                *self.indices)
            return self

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
                for a in funcof:
                    i += 1
                    da = a.diff(wrt)
                    if da is S.Zero:
                        continue
                    df = IndexedFunc(base_str.format(
                    str(self.base), str(a)), args=self.functional_form)[self.indices]
                    
                    l.append(df * da)
                return Add(*l)

        @property
        def free_symbols(self):
            return super(Indexed, self).free_symbols.union(*[
            set([x]) if not isinstance(x, IndexedFunc.IndexedFuncValue) else
            x.free_symbols for x in self._get_iter_func()])

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
            if self.shape and len(self.shape) != len(indices):
                raise IndexException("Rank mismatch.")
            return IndexedFunc.IndexedFuncValue(self,
                self.functional_form,
                *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return IndexedFunc.IndexedFuncValue(self,
                self.functional_form,
                indices, **kw_args)