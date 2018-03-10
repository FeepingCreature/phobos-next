import std.traits : isIntegral;
import std.meta : AliasSeq, NoDuplicates, anySatisfy, allSatisfy;
import traits_ex : allSame, allSameIterative, allSameTypeIterative, allSameTypeRecursive, allSameTypeHybrid, anySatisfyIterative, allSatisfyIterative;

struct W(T, size_t n)
{
    T value;
}

/** Fake comparsion for getting some kind of lower limit on compiler-built-in type comparison. */
enum allSameTypeFake(Ts...) = is(Ts[0 .. $/2] == Ts[$/2 .. $]);

enum allSameUsingNoDuplicates(Ts...) = NoDuplicates!Ts.length == 1;

void main()
{
    alias Ts(uint n) = AliasSeq!(W!(byte, n), W!(ubyte, n),
                                 W!(short, n), W!(ushort, n),
                                 W!(int, n), W!(uint, n),
                                 W!(long, n), W!(ulong, n),
                                 W!(float, n), W!(cfloat, n),
                                 W!(double, n), W!(cdouble, n),
                                 W!(real, n), W!(creal, n),
                                 W!(string, n), W!(wstring, n), W!(dstring, n));

    enum n = 500;              // number of different sets of instantations of Ts
    static foreach (i; 0 .. n)
    {
        // uncomment what you like and measure compilation speed:

        // static if (allSatisfyIterative!(isIntegral, Ts!(i))) {} // 0.9 secs
        // static if (allSatisfy!(isIntegral, Ts!(i))) {} // 7 secs

        // static if (anySatisfyIterative!(isIntegral, Ts!(i))) {} // 7 secs
        // static if (anySatisfy!(isIntegral, Ts!(i))) {}

        // static if (allSameIterative!(Ts!(i))) {} // 0.6 secs
        // static if (allSameUsingNoDuplicates!(Ts!(i))) {} // 9.3 secs
    }
}
