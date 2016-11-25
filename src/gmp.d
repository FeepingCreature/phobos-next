/** High-level wrapper for GNU Multiple Precision (MP) library.
 */
module gmp;

version(unittest)
{
    import dbgio : dln;
}

/** Arbitrary precision signed integer.
 */
struct Integer
{
    import std.typecons : Unqual;

    pragma(inline) @trusted pure nothrow @nogc:

    /// No copying be default.
    @disable this();

    /// Construct empty (undefined) from explicit `null`.
    this(typeof(null)) { __gmpz_init(_ptr); }

    /// Construct from `value`.
    this(long value) { __gmpz_init_set_si(_ptr, value); }

    /// Construct from `value`.
    this(ulong value) { __gmpz_init_set_ui(_ptr, value); }

    /// Construct from `value`.
    this(double value) { __gmpz_init_set_d(_ptr, value); }

    /// Construct from `value`.
    this(const string value)
    {
        const int status = __gmpz_init_set_str(_ptr, value.ptr, cast(int)value.length);
        assert(status == 0, "Parameter `value` does not contain an integer");
    }

    @disable this(this);

    /// Returns: deep copy (duplicate) of `this`.
    typeof(this) dup() const
    {
        typeof(return) y = void;
        __gmpz_init_set(y._ptr, _ptr);
        return y;
    }

    /// Destruct `this`.
    ~this()
    {
        if (_ptr) { __gmpz_clear(_ptr); }
    }

    // comparison
    bool opEquals(const ref typeof(this) rhs) const
    {
        return (_ptr == rhs._ptr || // fast compare
                __gmpz_cmp(_ptr, rhs._ptr) == 0);
    }
    bool opEquals(in typeof(this) rhs) const
    {
        return (_ptr == rhs._ptr || // fast compare
                __gmpz_cmp(_ptr, rhs._ptr) == 0);
    }
    bool opEquals(double rhs) const { return __gmpz_cmp_d(_ptr, rhs) == 0; }
    bool opEquals(long rhs) const { return __gmpz_cmp_si(_ptr, rhs) == 0; }
    bool opEquals(ulong rhs) const { return __gmpz_cmp_ui(_ptr, rhs) == 0; }

    // comparison
    int opCmp(const ref typeof(this) rhs) const { return __gmpz_cmp(_ptr, rhs._ptr); }
    int opCmp(in typeof(this) rhs) const { return __gmpz_cmp(_ptr, rhs._ptr); }
    int opCmp(double rhs) const { return __gmpz_cmp_d(_ptr, rhs); }
    int opCmp(long rhs) const { return __gmpz_cmp_si(_ptr, rhs); }
    int opCmp(ulong rhs) const { return __gmpz_cmp_ui(_ptr, rhs); }

    /// Add with `rhs`.
    Unqual!(typeof(this)) opBinary(string s)(const auto ref typeof(this) rhs) const
        if (s == "+")
    {
        typeof(return) y = null;
        __gmpz_add(y._ptr, this._ptr, rhs._ptr);
        return y;
    }
    /// ditto
    Unqual!(typeof(this)) opBinary(string s)(ulong rhs) const
        if (s == "+")
    {
        typeof(return) y = null;
        __gmpz_add_ui(y._ptr, this._ptr, rhs);
        return y;
    }

    /// Multiply with `rhs`.
    Unqual!(typeof(this)) opBinary(string s)(const auto ref typeof(this) rhs) const
        if (s == "*")
    {
        typeof(return) y = null;
        __gmpz_mul(y._ptr, this._ptr, rhs._ptr);
        return y;
    }
    /// ditto
    Unqual!(typeof(this)) opBinary(string s)(long rhs) const
        if (s == "*")
    {
        typeof(return) y = null;
        __gmpz_mul_si(y._ptr, this._ptr, rhs);
        return y;
    }
    /// ditto
    Unqual!(typeof(this)) opBinary(string s)(ulong rhs) const
        if (s == "*")
    {
        typeof(return) y = null;
        __gmpz_mul_ui(y._ptr, this._ptr, rhs);
        return y;
    }

    /// Returns: division remainder between `this` and `rhs`.
    Unqual!(typeof(this)) opBinary(string s)(const auto ref Integer rhs) const
        if (s == "%")
    {
        typeof(return) y = null;
        __gmpz_mod(y._ptr, this._ptr, rhs._ptr);
        return y;
    }

    private:

    inout(__mpz_struct)* _ptr() inout { return &_z; }

    __mpz_struct _z;
}

/// Returns: absolute value of `x`.
Integer abs(const ref Integer x) @trusted pure nothrow @nogc
{
    typeof(return) y = null;
    __gmpz_abs(y._ptr, x._ptr);
    return y;
}

@safe pure nothrow @nogc unittest
{
    alias Z = Integer;          // shorthand
    const Z a = 42L;
    const Z b = 43UL;
    const Z c = 43.0;
    const Z d = `101`;

    immutable Z ic = 101UL;

    assert(a == a.dup);
    assert(ic == ic.dup);

    // equality
    assert(a == a);
    assert(a == Z(42UL));
    assert(a == 42.0);
    assert(a == 42L);
    assert(a == 42UL);

    // non-equality
    assert(a != b);

    // less than
    assert(a < b);
    assert(a < Z(43UL));
    assert(a < 43L);
    assert(a < 43UL);
    assert(a < 43.0);

    // greater than
    assert(b > a);
    assert(b > Z(42UL));
    assert(b > 42L);
    assert(b > 42UL);
    assert(b > 42.0);

    // absolute value
    assert(abs(a) == a);
    assert(a.abs == a);         // UFCS

    // addition
    assert(a + b == b + a);
    assert(a + Z(43UL) == b + a);
    assert(a + 0UL == a);
    assert(a + 1UL != a);
    assert(a + b == 42UL + 43UL);

    // multiplication
    assert(a * 1UL == a);
    assert(a * 1L == a);
    assert(a * 2L != a);
    assert(a * b == b * a);
    assert(a * b == 42UL * 43UL);

    // modulo/remainder
    const Z one = 1UL;
    const Z two = 2UL;
    const Z three = 3UL;
    const Z four = 4UL;
    const Z five = 5UL;
    const Z six = 6UL;
    assert(six % one == 0L);
    assert(six % two == 0L);
    assert(six % three == 0L);
    assert(six % four == 2L);
    assert(six % five == 1L);
    assert(six % six == 0L);
}

// C API
extern(C)
{
    struct __mpz_struct
    {
        int _mp_alloc;		/* Number of *limbs* allocated and pointed to by
                                   the _mp_d field.  */
        int _mp_size;           /* abs(_mp_size) is the number of limbs the last
                                   field points to.  If _mp_size is negative
                                   this is a negative number.  */
        void* _mp_d;            /* Pointer to the limbs.  */
    }

    alias mpz_srcptr = const(__mpz_struct)*;
    alias mpz_ptr = __mpz_struct*;
    alias mp_bitcnt_t = ulong;

    pure nothrow @nogc:

    void __gmpz_init (mpz_ptr);
    void __gmpz_init_set (mpz_ptr, mpz_srcptr);

    void __gmpz_init_set_d (mpz_ptr, double);
    void __gmpz_init_set_si (mpz_ptr, long);
    void __gmpz_init_set_ui (mpz_ptr, ulong);
    int __gmpz_init_set_str (mpz_ptr, const char*, int);

    void __gmpz_clear (mpz_ptr);

    void __gmpz_abs (mpz_ptr, mpz_srcptr);

    void __gmpz_add (mpz_ptr, mpz_srcptr, mpz_srcptr);
    void __gmpz_add_ui (mpz_ptr, mpz_srcptr, ulong);
    void __gmpz_addmul (mpz_ptr, mpz_srcptr, mpz_srcptr);
    void __gmpz_addmul_ui (mpz_ptr, mpz_srcptr, ulong);

    void __gmpz_mul (mpz_ptr, mpz_srcptr, mpz_srcptr);
    void __gmpz_mul_2exp (mpz_ptr, mpz_srcptr, mp_bitcnt_t);
    void __gmpz_mul_si (mpz_ptr, mpz_srcptr, long);
    void __gmpz_mul_ui (mpz_ptr, mpz_srcptr, ulong);

    void __gmpz_mod (mpz_ptr, mpz_srcptr, mpz_srcptr);

    int __gmpz_cmp (mpz_srcptr, mpz_srcptr); // TODO: __GMP_NOTHROW __GMP_ATTRIBUTE_PURE;
    int __gmpz_cmp_d (mpz_srcptr, double); // TODO: __GMP_ATTRIBUTE_PURE
    int __gmpz_cmp_si (mpz_srcptr, long); // TODO: __GMP_NOTHROW __GMP_ATTRIBUTE_PURE
    int __gmpz_cmp_ui (mpz_srcptr, ulong); // TODO: __GMP_NOTHROW __GMP_ATTRIBUTE_PURE
}

pragma(lib, "gmp");
