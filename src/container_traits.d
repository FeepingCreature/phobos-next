/** Traits used by containers. */
module container_traits;

template ContainerElementType(ContainerType,
                              ElementType)
{
    import std.traits : isMutable, hasIndirections, PointerTarget, isPointer,
        Unqual;

    template ET(bool isConst, T)
    {
        static if (isPointer!ElementType)
        {
            enum PointerIsConst = is(ElementType == const);
            enum PointerIsImmutable = is(ElementType == immutable);
            enum DataIsConst = is(PointerTarget!ElementType == const);
            enum DataIsImmutable = is(PointerTarget!ElementType == immutable);
            static if (isConst)
            {
                static if (PointerIsConst)
                {
                    alias ET = ElementType;
                }
                else static if (PointerIsImmutable)
                {
                    alias ET = ElementType;
                }
                else
                {
                    alias ET = const(PointerTarget!ElementType)*;
                }
            }
            else
            {
                static assert(DataIsImmutable,
                              "An immutable container cannot reference const or mutable data");
                static if (PointerIsConst)
                {
                    alias ET = immutable(PointerTarget!ElementType)*;
                }
                else
                {
                    alias ET = ElementType;
                }
            }
        }
        else
        {
            static if (isConst)
            {
                static if (is(ElementType == immutable))
                {
                    alias ET = ElementType;
                }
                else
                {
                    alias ET = const(Unqual!ElementType);
                }
            }
            else
            {
                alias ET = immutable(Unqual!ElementType);
            }
        }
    }

    static if (isMutable!ContainerType)
    {
        alias ContainerElementType = ElementType;
    }
    else
    {
        static if (hasIndirections!ElementType)
        {
            alias ContainerElementType = ET!(is(ContainerType == const), ElementType);
        }
        else
        {
            alias ContainerElementType = ElementType;
        }
    }
}

/**
 * This enum must be used as an UDA to mark a variable of a type that looks
 * like GC-managed but that is actually not GC-managed.
 */
enum NoGc;

/**
 * When this enum is used as UDA on aggregate types whose instances are
 * created with construct() a compile time message indicates if a GC range
 * will be added for the members.
 */
enum TellRangeAdded;

/**
 * Indicates if an aggregate contains members that might be collected by the
 * garbage collector. This is used in constructors to determine if the content
 * of a manually allocated aggregate must be declared to the GC.
 */
template mustAddGCRange(T)
    if (is(T == struct) ||
        is(T == union) ||
        is(T == class)) // isAggregateType!T
{
    import std.traits : hasUDA, isDynamicArray, isPointer;

    string check()
    {
        string managedMembers;

        enum addManaged = q{managedMembers ~= " " ~ T.tupleof[i].stringof;};

        static if (is(T == class))
        {
            import std.traits : BaseClassesTuple;

            foreach (BT; BaseClassesTuple!T)
            {
                string m = mustAddGCRange!BT;
                if (m.length)
                {
                    managedMembers ~= " " ~ m;
                }
            }
        }

        import std.meta : aliasSeqOf;
        import std.range : iota;
        version(LDC) static if (__VERSION__ >= 2076) { static assert(0, "TODO use static foreach (i; 0, T.tupleof.length) instead"); }
        foreach (i; aliasSeqOf!(iota(0, T.tupleof.length))) // TODO use my iota!(0, T.tupleof.length)
        {
            static if (!is(typeof(T.tupleof[i]) == void))
            {
                alias MT = typeof(T.tupleof[i]);
                static if (isDynamicArray!MT &&
                           !hasUDA!(T.tupleof[i], NoGc))
                {
                    mixin(addManaged);
                }
                else static if (isPointer!MT &&
                                !hasUDA!(T.tupleof[i], NoGc))
                {
                    mixin(addManaged);
                }
                else static if (is(MT == class) &&
                                (!is(MT : T)) &&
                                !hasUDA!(T.tupleof[i], NoGc) &&
                                !(isTemplateInstance!T /*&& staticIndexOf!(MT,TemplateArgsOf!T) > 0*/ ))
                {
                    // failure here when the class is a template and when one of the member
                    // type is one of the template argument.
                    //pragma(msg, T.stringof, " ", MT.stringof);
                    static if (mustAddGCRange!MT)
                    {
                        mixin(addManaged);
                    }
                }
                else static if (is(MT == struct) &&
                                !is(MT == T) &&
                                !hasUDA!(T.tupleof[i], NoGc))
                {
                    static if (mustAddGCRange!MT)
                    {
                        mixin(addManaged);
                    }
                }
                else static if (is(MT == union) &&
                                !is(MT == T) &&
                                !hasUDA!(T.tupleof[i], NoGc))
                {
                    static if (mustAddGCRange!MT)
                    {
                        mixin(addManaged);
                    }
                }
            }
        }
        return managedMembers;
    }

    static if (hasUDA!(T, NoGc))
    {
        enum mustAddGCRange = [];
    }
    else
    {
        enum mustAddGCRange = check();
    }

    static if (hasUDA!(T, TellRangeAdded))
    {
        static if (mustAddGCRange.length)
        {
            pragma(msg,
                   "a GC range will be added for any new " ~ T.stringof
                   ~ ", because of: " ~ mustAddGCRange);
        }
        else
        {
            pragma(msg, "a GC range wont be added for any new " ~ T.stringof);
        }
    }
}

/// ditto
template mustAddGCRange(T)
    if (!(is(T == struct) ||
          is(T == union) ||
          is(T == class))) // !isAggregateType!T
{
    import std.traits : isStaticArray;
    static if (isStaticArray!T)
    {
        enum mustAddGCRange = T.length >= 1 && mustAddGCRange!(typeof(T.init[0]));
    }
    else
    {
        // TODO optimize this dumb overload
        struct Dummy { T t; }
        enum mustAddGCRange = mustAddGCRange!Dummy;
    }
}

/// Returns: `true` iff `T` is a template instance, `false` otherwise.
private template isTemplateInstance(T)
{
    import std.traits : TemplateOf;
    enum isTemplateInstance = is(typeof(TemplateOf!(T)));
}

///
@safe pure nothrow @nogc unittest
{
    static assert(!mustAddGCRange!int);
    static assert(mustAddGCRange!(int*));
    static assert(mustAddGCRange!(int*[1]));
    static assert(!mustAddGCRange!(int*[0]));
    static assert(mustAddGCRange!(int[]));

    class Foo
    {
        @NoGc int[] a;
        @NoGc void* b;
    }
    static assert(!mustAddGCRange!Foo);

    class Bar
    {
        int[] a;
        @NoGc void* b;
    }
    static assert(mustAddGCRange!Bar);

    class Baz : Bar
    {
        @NoGc void* c;
    }
    static assert(mustAddGCRange!Baz);

    struct S
    {
        int x;
    }
    static assert(!mustAddGCRange!S);

    struct T
    {
        int* x;
    }
    static assert(mustAddGCRange!T);
    static assert(mustAddGCRange!(T[1]));

    struct U
    {
        @NoGc int* x;
    }
    static assert(!mustAddGCRange!U);
    static assert(!mustAddGCRange!(U[1]));

    union N
    {
        S s;
        U u;
    }
    static assert(!mustAddGCRange!N);
    static assert(!mustAddGCRange!(N[1]));

    union M
    {
        S s;
        T t;
    }
    static assert(mustAddGCRange!M);
    static assert(mustAddGCRange!(M[1]));
}
