from sympy.core.compatibility import with_metaclass
from sympy.core.singleton import Singleton, S
from sympy.core.numbers import NumberSymbol, mpf_norm, Integer
from mpmath.libmp.libmpf import from_float

"""
Static symbols -- constants in the code, associated with a symbol
"""
class mass(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    m_val = 1

    def _latex(self, printer):
        return r"m"

    @staticmethod
    def abs():
        return S.mass

    def __int__(self):
        return self.m_val

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.m_val), Integer(self.m_val))
        elif issubclass(number_cls, Rational):
            return (Rational(self.m_val, self.m_val), Rational(self.m_val, self.m_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.m_val)
        return mpf_norm(rv, prec)

class volume(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    v_val = 1

    def _latex(self, printer):
        return r"V"

    @staticmethod
    def abs():
        return S.volume

    def __int__(self):
        return self.v_val

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.v_val), Integer(self.v_val))
        elif issubclass(number_cls, Rational):
            return (Rational(self.v_val, self.v_val), Rational(self.v_val, self.v_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.v_val)
        return mpf_norm(rv, prec)

class pressure(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    p_val = 101325

    def _latex(self, printer):
        return r"P"

    @staticmethod
    def abs():
        return S.pressure

    def __int__(self):
        return self.p_val

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.p_val), Integer(self.p_val))
        elif issubclass(number_cls, Rational):
            return (Rational(self.p_val, self.p_val), Rational(self.p_val, self.p_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.p_val)
        return mpf_norm(rv, prec)

class atm_pressure(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    p_val = 101325

    def _latex(self, printer):
        return r"P_{atm}"

    @staticmethod
    def abs():
        return S.pressure

    def __int__(self):
        return self.p_val

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.p_val), Integer(self.p_val))
        elif issubclass(number_cls, Rational):
            return (Rational(self.p_val, self.p_val), Rational(self.p_val, self.p_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.p_val)
        return mpf_norm(rv, prec)

class gas_constant(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_positive = True
    is_negative = False
    is_irrational = True
    is_number = True
    is_algebraic = False
    is_transcendental = True
    r_val = 8.3144621

    def _latex(self, printer):
        return r"{R_u}"

    @staticmethod
    def abs():
        return S.gas_constant

    def __int__(self):
        return int(self.r_val)

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.r_val), Integer(self.r_val + 1))
        elif issubclass(number_cls, Rational):
            return (Rational(self.r_val, self.r_val), Rational(self.r_val, self.r_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.r_val)
        return mpf_norm(rv, prec)

class Ns(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_integer = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    r_val = 10

    def _latex(self, printer):
        return r"N_s"

    @staticmethod
    def abs():
        return S.Ns

    def __int__(self):
        return int(self.r_val)

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.r_val), Integer(self.r_val + 1))
        elif issubclass(number_cls, Rational):
            return (Rational(self.r_val, self.r_val), Rational(self.r_val, self.r_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.r_val)
        return mpf_norm(rv, prec)

class Nr(with_metaclass(Singleton, NumberSymbol)):
    is_real = True
    is_integer = True
    is_positive = True
    is_negative = False
    is_irrational = False
    is_number = True
    is_algebraic = True
    is_transcendental = False
    r_val = 100

    def _latex(self, printer):
        return r"N_r"

    @staticmethod
    def abs():
        return S.Nr

    def __int__(self):
        return int(self.r_val)

    def approximation_interval(self, number_cls):
        if issubclass(number_cls, Integer):
            return (Integer(self.r_val), Integer(self.r_val + 1))
        elif issubclass(number_cls, Rational):
            return (Rational(self.r_val, self.r_val), Rational(self.r_val, self.r_val))

    def _as_mpf_val(self, prec):
        rv = from_float(self.r_val)
        return mpf_norm(rv, prec)