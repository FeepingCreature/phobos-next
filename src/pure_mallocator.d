module pure_mallocator;

import std.experimental.allocator.common;

/**
   The C heap allocator purified.
 */
struct PureMallocator
{
    pure nothrow @nogc:

    /**
     * The alignment is a static constant equal to $(D platformAlignment), which
     * ensures proper alignment for any D data type.
    */
    enum uint alignment = platformAlignment;

    /**
     * Standard allocator methods per the semantics defined above. The
     * $(D deallocate) and $(D reallocate) methods are $(D @system) because they
     * may move memory around, leaving dangling pointers in user code. Somewhat
     * paradoxically, $(D malloc) is $(D @safe) but that's only useful to safe
     * programs that can afford to leak memory allocated.
     */
    pragma(inline, true)
    void[] allocate(size_t bytes) shared
        @trusted
    {
        import core.memory : pureMalloc;
        if (!bytes) return null;
        void* p = pureMalloc(bytes);
        return p ? p[0 .. bytes] : null;
    }

    pragma(inline, true)
    void[] zeroallocate(size_t bytes) shared
        @trusted
    {
        import core.memory : pureCalloc;
        if (!bytes) return null;
        void* p = pureCalloc(bytes, 1);
        return p ? p[0 .. bytes] : null;
    }

    /// Ditto
    pragma(inline, true)
    bool deallocate(void[] b) shared
        @system
    {
        import core.memory : pureFree;
        pureFree(b.ptr);        // b.length not needed
        return true;
    }

    /// Ditto
    bool reallocate(ref void[] b, size_t s) shared
        @system
    {
        import core.memory : pureRealloc;
        if (!s)
        {
            // fuzzy area in the C standard, see http://goo.gl/ZpWeSE
            // so just deallocate and nullify the pointer
            deallocate(b);
            b = null;
            return true;
        }
        ubyte* p = cast(ubyte*)pureRealloc(b.ptr, s);
        if (!p) return false;
        b = p[0 .. s];
        return true;
    }

    /**
     * Returns the global instance of this allocator type. The C heap allocator is
     * thread-safe, therefore all of its methods and `it` itself are
     * $(D shared).
     */
    static shared PureMallocator instance;
}

@safe pure unittest
{
    // TODO auto buf = PureMallocator.instance.allocate(16);
}
