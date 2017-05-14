/** File I/O of Compressed Files.
*/
module zio;

struct GzipFileInputRange
{
    import std.stdio : File;
    import std.traits : ReturnType;

    enum chunkSize = 0x4000;

    this(in const(char)[] path)
    {
        _f = File(path, "r");
        _chunkRange = _f.byChunk(chunkSize);
        _uncompress = new UnCompress;
        loadNextChunk();
    }

    void loadNextChunk()
    {
        if (!_chunkRange.empty)
        {
            _uncompressedBuf = cast(ubyte[])_uncompress.uncompress(_chunkRange.front);
            _chunkRange.popFront();
        }
        else
        {
            if (!_exhausted)
            {
                _uncompressedBuf = cast(ubyte[])_uncompress.flush();
                _exhausted = true;
            }
            else
            {
                _uncompressedBuf.length = 0;
            }
        }
        _bufIx = 0;
    }

    void popFront()
    {
        _bufIx += 1;
        if (_bufIx >= _uncompressedBuf.length)
        {
            loadNextChunk();
        }
    }

    pragma(inline, true):
    @safe pure nothrow @nogc:

    @property ubyte front() const
    {
        return _uncompressedBuf[_bufIx];
    }

    @property bool empty() const
    {
        return _uncompressedBuf.length == 0;
    }

private:
    import std.zlib: UnCompress;
    UnCompress _uncompress;
    File _f;
    ReturnType!(_f.byChunk) _chunkRange;
    bool _exhausted;
    ubyte[] _uncompressedBuf;
    size_t _bufIx;
}

class GzipByLine
{
    private alias E = char;

    this(in const(char)[] path,
         E separator = '\n')
    {
        this._range = typeof(_range)(path);
        this._separator = separator;
        // this._lbuf = typeof(_lbuf).withCapacity(80);
        popFront();
    }

    void popFront()
    {
        _lbuf.shrinkTo(0);

        static if (__traits(hasMember, typeof(_range), `bufferFronts`) &&
                   __traits(hasMember, typeof(_range), `loadNextChunk`) &&
                   __traits(hasMember, typeof(_range), `put`)) // TODO use trait
        {
            // TODO functionize
            import std.algorithm.searching : find;
            while (!_range.empty)
            {
                ubyte[] currentFronts = _range.bufferFronts;
                // `_range` is mutable so sentinel-based search can kick
                const hit = currentFronts.find(_separator); // or use `indexOf`
                if (hit.length)
                {
                    const lineLength = hit.ptr - currentFronts.ptr;
                    _lbuf.put(currentFronts[0 .. lineLength]); // add everything to separator
                    _range._bufIx += lineLength + _separator.sizeof; // advancement + separator
                    if (_range.empty)
                    {
                        _range.loadNextChunk();
                    }
                    break;      // done
                }
                else            // no separator yet
                {
                    _lbuf.put(currentFronts); // so just add everything
                    _range.loadNextChunk();
                }
            }
        }
        else
        {
            // TODO sentinel-based search for `_separator` in `_range`
            while (!_range.empty &&
                   _range.front != _separator)
            {
                _lbuf.put(_range.front);
                _range.popFront();
            }

            if (!_range.empty &&
                _range.front == _separator)
            {
                _range.popFront();  // pop separator
            }
        }
    }

    pragma(inline, true):
    @safe pure nothrow @nogc:

    @property bool empty()
    {
        return _lbuf.data.length == 0;
    }

    const(E)[] front() const return scope
    {
        return _lbuf.data;
    }

private:
    ZlibFileInputRange _range;

    import std.array : Appender;
    Appender!(E[]) _lbuf;    // line buffer

    // NOTE this is slower for ldc:
    // import array_ex : UniqueArray;
    // UniqueArray!E _lbuf;

    E _separator;
}

class GzipOut
{
    import std.zlib: Compress, HeaderFormat;
    import std.stdio: File;

    this(File file)
    {
        _f = file;
        _compress = new Compress(HeaderFormat.gzip);
    }

    void compress(const string s)
    {
        auto compressed = _compress.compress(s);
        _f.rawWrite(compressed);
    }

    void finish()
    {
        auto compressed = _compress.flush;
        _f.rawWrite(compressed);
        _f.close;
    }

private:
    Compress _compress;
    File _f;
}

struct ZlibFileInputRange
{
    enum defaultExtension = `.gz`;

    /* Zlib docs:
       CHUNK is simply the buffer size for feeding data to and pulling data from
       the zlib routines. Larger buffer sizes would be more efficient,
       especially for inflate(). If the memory is available, buffers sizes on
       the order of 128K or 256K bytes should be used.
    */
    enum chunkSize = 128 * 1024; // 128K

    @safe:

    this(in const(char)[] path) @trusted
    {
        import std.string : toStringz; // TODO avoid GC allocation by looking at how gmp-d z.d solves it
        _f = gzopen(path.toStringz, `rb`);
        if (!_f)
        {
            throw new Exception("Couldn't open file " ~ path.idup);
        }
        _buf = new ubyte[chunkSize];
        loadNextChunk();
    }

    ~this() @trusted
    {
        const int ret = gzclose(_f);
        if (ret < 0)
        {
            throw new Exception("Couldn't close file");
        }
    }

    @disable this(this);

    void loadNextChunk() @trusted
    {
        int count = gzread(_f, _buf.ptr, chunkSize);
        if (count == -1)
        {
            throw new Exception("Error decoding file");
        }
        _bufIx = 0;
        _bufReadLength = count;
    }

    void popFront()
    {
        assert(!empty);
        _bufIx += 1;
        if (_bufIx >= _bufReadLength)
        {
            loadNextChunk();
            _bufIx = 0;         // restart counter
        }
    }

    pragma(inline, true):
    pure nothrow @nogc:

    @property ubyte front() const @trusted
    {
        assert(!empty);
        return _buf.ptr[_bufIx];
    }

    @property bool empty() const
    {
        return _bufIx == _bufReadLength;
    }

    /** Get current bufferFronts.
        TODO need better name for this
     */
    inout(ubyte)[] bufferFronts() inout @trusted
    {
        assert(!empty);
        return _buf.ptr[_bufIx .. _bufReadLength];
    }

private:
    import etc.c.zlib : gzFile, gzopen, gzclose, gzread;

    gzFile _f;

    ubyte[] _buf;               // block read buffer

    // number of bytes in `_buf` recently read by `gzread`, normally equal to `_buf.length` except after last read where is it's normally less than `_buf.length`
    size_t _bufReadLength;

    size_t _bufIx;              // current stream read index in `_buf`

    // TODO make this work:
    // extern (C) nothrow @nogc:
    // pragma(mangle, "gzopen") gzFile gzopen(const(char)* path, const(char)* mode);
    // pragma(mangle, "gzclose") int gzclose(gzFile file);
    // pragma(mangle, "gzread") int gzread(gzFile file, void* buf, uint len);
}

struct Bz2libFileInputRange
{
    enum chunkSize = 128 * 1024; // 128K
    enum defaultExtension = `.bz2`;

    @safe:

    this(in const(char)[] path) @trusted
    {
        import std.string : toStringz; // TODO avoid GC allocation by looking at how gmp-d z.d solves it
        _f = BZ2_bzopen(path.toStringz, `rb`);
        if (!_f)
        {
            throw new Exception("Couldn't open file " ~ path.idup);
        }
        _buf = new ubyte[chunkSize];
        loadNextChunk();
    }

    ~this() @trusted
    {
        BZ2_bzclose(&_f);       // TODO error handling?
    }

    @disable this(this);

    void loadNextChunk() @trusted
    {
        int count = BZ2_bzread(_f, _buf.ptr, chunkSize);
        if (count == -1)
        {
            throw new Exception("Error decoding file");
        }
        _bufIx = 0;
        _bufReadLength = count;
    }

    void popFront()
    {
        assert(!empty);
        _bufIx += 1;
        if (_bufIx >= _bufReadLength)
        {
            loadNextChunk();
            _bufIx = 0;         // restart counter
        }
    }

    pragma(inline, true):
    pure nothrow @nogc:

    @property ubyte front() const @trusted
    {
        assert(!empty);
        return _buf.ptr[_bufIx];
    }

    @property bool empty() const
    {
        return _bufIx == _bufReadLength;
    }

    /** Get current bufferFronts.
        TODO need better name for this
     */
    inout(ubyte)[] bufferFronts() inout @trusted
    {
        assert(!empty);
        return _buf.ptr[_bufIx .. _bufReadLength];
    }

private:
    import bzlib : BZFILE, BZ2_bzopen, BZ2_bzread, BZ2_bzwrite, BZ2_bzclose;
    pragma(lib, "bz2");             // Ubuntu: sudo apt-get install libbz2-dev

    BZFILE* _f;

    ubyte[] _buf;               // block read buffer

    // number of bytes in `_buf` recently read by `gzread`, normally equal to `_buf.length` except after last read where is it's normally less than `_buf.length`
    size_t _bufReadLength;

    size_t _bufIx;              // current stream read index in `_buf`
}

void testInputRange(FileInputRange)()
{
    import std.stdio : File;

    enum path = "test" ~ FileInputRange.defaultExtension;

    const wholeSource = "abc\ndef\nghi";

    foreach (const n; 4 .. wholeSource.length) // TODO change 4 to 0
    {
        dln(`n:`, n);
        const source = wholeSource[0 .. n]; // slice from the beginning
        dln(`source:"`, source, `"`);

        scope File file = File(path, "w"); // TODO temporary file
        scope auto of = new GzipOut(file);
        of.compress(source);
        of.finish();

        size_t ix = 0;
        foreach (e; FileInputRange(path))
        {
            assert(cast(char)e == source[ix]);
            ++ix;
        }

        import std.algorithm.searching : count;
        import std.algorithm.iteration : splitter;
        assert(new GzipByLine(path).count == source.splitter('\n').count);
    }
}

unittest
{
    testInputRange!(ZlibFileInputRange);
    // TODO activate testInputRange!(Bz2libFileInputRange);
}

version(none)
unittest
{
    enum path = "/home/per/Knowledge/ConceptNet5/5.5/conceptnet-assertions-5.5.0.csv.gz";

    import std.stdio: writeln;
    import std.range: take;
    import std.algorithm.searching: count;

    const lineBlockCount = 100_000;
    size_t lineNr = 0;
    foreach (const line; new GzipByLine(path))
    {
        if (lineNr % lineBlockCount == 0)
        {
            writeln(`Line `, lineNr, ` read containing:`, line);
        }
        lineNr += 1;
    }

    const lineCount = 5;
    foreach (const line; new GzipByLine(path).take(lineCount))
    {
        writeln(line);
    }
}

version(unittest)
{
    import std.stdio : write, writeln;
    import dbgio : dln;
}
