/** xxHash is an extremely fast non-cryptographic hash algorithm, working at
    speeds close to RAM limits. It is proposed in two flavors, 32 and 64 bits.

    TODO merge into xxhash-d
*/
module xxhash64;

@safe pure nothrow @nogc:

/** Compute xxHash-64 of input `data`, with optional seed `seed`.
 */
ulong xxhash64Of(in ubyte[] data, ulong seed = 0)
    @trusted
{
    auto xh = XXHash64(seed);
    xh.start();
    xh.put(data.ptr, data.length);
    return xh.finish();
}
/// ditto
ulong xxhash64Of(in string data, ulong seed = 0)
    @trusted
{
    return xxhash64Of(cast(ubyte[])data, seed);
}

/** xxHash-64, based on Yann Collet's descriptions

    How to use:

        ulong myseed = 0;
        XXHash64 myhash(myseed);
        myhash.put(pointerToSomeBytes,     numberOfBytes);
        myhash.put(pointerToSomeMoreBytes, numberOfMoreBytes); // call put() as often as you like to ...

    and compute hash:

        ulong result = myhash.hash();

    or all of the above in one single line:

        ulong result2 = XXHash64::hashOf(mypointer, numBytes, myseed);

    See also: http://cyan4973.github.io/xxHash/
    See also: http://create.stephan-brumme.com/xxhash/

    TODO make endian-aware
**/
struct XXHash64
{
    @safe pure nothrow @nogc:

    /**
     * Constructs XXHash64 with `seed`.
     */
    this(ulong seed)
    {
        _seed = seed;
    }

    /** (Re)initialize.
     */
    void start()
    {
        state[0] = _seed + prime1 + prime2;
        state[1] = _seed + prime2;
        state[2] = _seed;
        state[3] = _seed - prime1;
        bufferSize  = 0;
        totalLength = 0;
    }

    /// Add a chunk of bytes.
    /** @param  data  pointer to a continuous block of data
        @param  length number of bytes
        @return false if parameters are invalid / zero **/
    bool put(scope const(ubyte)* data, ulong length) @trusted
    {
        // no data ?
        if (!data || length == 0)
        {
            return false;
        }

        totalLength += length;

        // unprocessed old data plus new data still fit in temporary buffer ?
        if (bufferSize + length < bufferMaxSize)
        {
            // just add new data
            while (length-- > 0)
            {
                buffer[bufferSize++] = *data++;
            }
            return true;
        }

        // point beyond last byte
        const(ubyte)* stop      = data + length;
        const(ubyte)* stopBlock = stop - bufferMaxSize;

        // some data left from previous update ?
        if (bufferSize > 0)
        {
            // make sure temporary buffer is full (16 bytes)
            while (bufferSize < bufferMaxSize)
            {
                buffer[bufferSize++] = *data++;
            }

            // process these 32 bytes (4x8)
            process(buffer.ptr, state[0], state[1], state[2], state[3]);
        }

        // copying state to local variables helps optimizer A LOT
        ulong s0 = state[0], s1 = state[1], s2 = state[2], s3 = state[3];
        // 32 bytes at once
        while (data <= stopBlock)
        {
            // local variables s0..s3 instead of state[0]..state[3] are much faster
            process(data, s0, s1, s2, s3);
            data += 32;
        }
        // copy back
        state[0] = s0; state[1] = s1; state[2] = s2; state[3] = s3;

        // copy remainder to temporary buffer
        bufferSize = stop - data;
        for (uint i = 0; i < bufferSize; i++)
        {
            buffer[i] = data[i];
        }

        // done
        return true;
    }

    /** Returns: the finished XXHash64 hash.
        This also calls $(LREF start) to reset the internal state.
    */
    ulong finish() @trusted
    {
        // fold 256 bit state into one single 64 bit value
        ulong result;
        if (totalLength >= bufferMaxSize)
        {
            result = (rotateLeft(state[0],  1) +
                      rotateLeft(state[1],  7) +
                      rotateLeft(state[2], 12) +
                      rotateLeft(state[3], 18));
            result = (result ^ processSingle(0, state[0])) * prime1 + prime4;
            result = (result ^ processSingle(0, state[1])) * prime1 + prime4;
            result = (result ^ processSingle(0, state[2])) * prime1 + prime4;
            result = (result ^ processSingle(0, state[3])) * prime1 + prime4;
        }
        else
        {
            // internal state wasn't set in put(), therefore original seed is still stored in state2
            result = state[2] + prime5;
        }

        result += totalLength;

        // process remaining bytes in temporary buffer
        const(ubyte)* data = buffer.ptr;

        // point beyond last byte
        const(ubyte)* stop = data + bufferSize;

        // at least 8 bytes left ? => eat 8 bytes per step
        for (; data + 8 <= stop; data += 8)
        {
            result = rotateLeft(result ^ processSingle(0, *cast(ulong*)data), 27) * prime1 + prime4;
        }

        // 4 bytes left ? => eat those
        if (data + 4 <= stop)
        {
            result = rotateLeft(result ^ (*cast(uint*)data) * prime1, 23) * prime2 + prime3;
            data  += 4;
        }

        // take care of remaining 0..3 bytes, eat 1 byte per step
        while (data != stop)
        {
            result = rotateLeft(result ^ (*data++) * prime5, 11) * prime1;
        }

        // mix bits
        result ^= result >> 33;
        result *= prime2;
        result ^= result >> 29;
        result *= prime3;
        result ^= result >> 32;

        start();

        return result;
    }

private:
    /// magic constants
    enum ulong prime1 = 11400714785074694791UL;
    enum ulong prime2 = 14029467366897019727UL;
    enum ulong prime3 =  1609587929392839161UL;
    enum ulong prime4 =  9650029242287828579UL;
    enum ulong prime5 =  2870177450012600261UL;

    /// temporarily store up to 31 bytes between multiple put() calls
    enum bufferMaxSize = 31+1;

    ulong[4] state;
    ubyte[bufferMaxSize] buffer;
    ulong bufferSize;
    ulong totalLength;

    ulong _seed;

    /// rotate bits, should compile to a single CPU instruction (ROL)
    static ulong rotateLeft(ulong x, ubyte bits)
    {
        return (x << bits) | (x >> (64 - bits));
    }

    /// process a single 64 bit value
    static ulong processSingle(ulong previous, ulong data)
    {
        return rotateLeft(previous + data * prime2, 31) * prime1;
    }

    /// process a block of 4x4 bytes, this is the main part of the XXHash32 algorithm
    static void process(const(ubyte)* data,
                        out ulong state0,
                        out ulong state1,
                        out ulong state2,
                        out ulong state3) @trusted
    {
        const(ulong)* block = cast(const(ulong)*)data;
        state0 = processSingle(state0, block[0]);
        state1 = processSingle(state1, block[1]);
        state2 = processSingle(state2, block[2]);
        state3 = processSingle(state3, block[3]);
    }
}

///
unittest
{
    ubyte[8] x = [1, 2, 3, 4, 5, 6, 7, 8];
    auto y = xxhash64Of(x[]);
    assert(xxhash64Of(x[]) == 9316896406413536788UL);

    // tests copied from https://pypi.python.org/pypi/xxhash/0.6.0
    assert(xxhash64Of(`xxhash`) == 3665147885093898016UL);
    assert(xxhash64Of(`xxhash`, 20141025) == 13067679811253438005UL);
}
