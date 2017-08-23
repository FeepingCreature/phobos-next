/** SUO-KIF File Format.

    See: https://en.wikipedia.org/wiki/Knowledge_Interchange_Format
    See: http://sigmakee.cvs.sourceforge.net/viewvc/sigmakee/sigma/suo-kif.pdf
*/
module suokif;

/** SUO-KIF (Lisp) Token Type. */
enum TOK
{
    unknown,

    leftParen,
    rightParen,

    symbol,

    stringLiteral,

    lispComma,
    lispBackQuote,
    lispQuote,

    variable,
    variableList,               // one or more variables (parameters)
    functionName,

    number,

    comment,
    whitespace,
}

/** SUO-KIF Token. */
struct Token
{
    @safe pure nothrow @nogc:
    TOK tok;
    string src;                 // optional source slice
}

/** SUO_KIF Expression.
    TODO use vary.FastVariant instead of `Expr[]`
 */
struct Expr
{
    Token token;                // token
    Expr[] subs;
}

import arrayn : ArrayN, Checking;
alias Exprs = ArrayN!(Expr, 128, Checking.viaScope);

/** Returns: true if `s` is null-terminated (ending with `'\0'`).

    Used to verify input to parser make use of sentinel-based search.

    See also: https://en.wikipedia.org/wiki/Sentinel_value
 */
pragma(inline, true)
bool isNullTerminated(const(char)[] s)
    @safe pure nothrow @nogc
{
    return s.length >= 1 && s[$ - 1] == '\0';
}

/** Parse SUO-KIF from `src` into returned array of expressions (`Expr`).
 */
struct SUOKIFParser
{
    import std.algorithm : among;

    private alias Src = string;

    @safe pure:

    this(Src input,
         bool includeComments = false,
         bool includeWhitespace = false)
    {
        _input = input;

        import std.algorithm : startsWith;
        immutable magic = x"EFBBBF";
        if (_input[_off .. $].startsWith(magic))
        {
            _off += magic.length;
        }

        import std.exception : enforce;
        enforce(_input.isNullTerminated); // safest to do this check in non-debug mode aswell

        _includeComments = includeComments;
        _includeWhitespace = includeWhitespace;

        nextFront();
    }

    pragma(inline, true)
    @property bool empty() const nothrow @nogc
    {
        return _endOfFile;
    }

    pragma(inline, true)
    ref Expr front() return scope
    {
        assert(!empty);
        return exprs.back;
    }

    pragma(inline, true)
    void popFront()
    {
        assert(!empty);
        exprs.popBack();
        nextFront();
    }

    import std.meta : AliasSeq;
    // from std.ascii.isWhite
    alias whiteChars = AliasSeq!(' ', // 0x20
                                 '\t', // (0x09)
                                 '\n', // (0x0a)
                                 '\v', // (0x0b)
                                 '\r', // (0x0c)
                                 '\f'); // (0x0d)
    alias digitChars = AliasSeq!('0', '1', '2', '3', '4', '5', '6', '7', '8', '9'); // TODO use benchmark

private:

    /// Get next `char` in input.
    pragma(inline, true)
    char peekNextChar() const nothrow @nogc
    {
        return _input[_off];    // TODO .ptr
    }

    /// Get next `char` in input.
    pragma(inline, true)
    char peekNextNthChar(size_t n) const nothrow @nogc
    {
        return _input[_off + n]; // TODO .ptr
    }

    /// Get next n `chars` in input.
    pragma(inline, true)
    Src peekNChars(size_t n) const nothrow @nogc
    {
        return _input[_off .. _off + n]; // TODO .ptr
    }

    /// Drop next byte in input.
    pragma(inline, true)
    void dropFront() nothrow @nogc
    {
        _off += 1;
    }

    /// Drop next `n` bytes in input.
    pragma(inline, true)
    void dropFrontN(size_t n) nothrow @nogc
    {
        _off += n;
    }

    /// Skip over `n` bytes in `src`.
    pragma(inline)
    Src skipOverNBytes(size_t n)
        nothrow @nogc
    {
        const part = _input[_off .. _off + n]; // TODO .ptr
        dropFrontN(n);
        return part;
    }

    /// Skip comment.
    pragma(inline)
    void skipComment()
    {
        while (!peekNextChar().among('\r', '\n')) // until end of line
        {
            _off += 1;
        }
    }

    /// Get symbol.
    pragma(inline)
    Src getSymbol() nothrow @nogc
    {
        size_t i = 0;
        while ((!peekNextNthChar(i).among!('\0', '(', ')',
                                           whiteChars))) // NOTE this is faster than !src[i].isWhite
        {
            ++i;
        }
        return skipOverNBytes(i);
    }

    /// Get numeric literal (number) in integer or decimal form.
    pragma(inline)
    Src getNumber() nothrow @nogc
    {
        size_t i = 0;
        while (peekNextNthChar(i).among!('+', '-', '.',
                                         digitChars)) // NOTE this is faster than src[i].isDigit
        {
            ++i;
        }
        return skipOverNBytes(i);
    }

    /// Skip whitespace.
    pragma(inline)
    Src getWhitespace() nothrow @nogc
    {
        size_t i = 0;
        while (peekNextNthChar(i).among!(whiteChars)) // NOTE this is faster than `src[i].isWhite`
        {
            ++i;
        }
        return skipOverNBytes(i);
    }

    /// Get string literal at `src`.
    pragma(inline)
    Src getStringLiteral() nothrow @nogc
    {
        dropFront();
        size_t i = 0;
        while (!peekNextNthChar(i).among('\0', '"')) // TODO handle backslash + double-quote
        {
            ++i;
        }
        const literal = peekNChars(i);
        dropFrontN(i);
        if (peekNextChar() == '"') { dropFront(); } // pop ending double quote
        return literal;
    }

    void nextFront()
    {
        import std.range : empty, front, popFront, popFrontN;
        import std.uni : isWhite, isAlpha;
        import std.ascii : isDigit;

        while (true)
        {
            switch (_input[_off]) // TODO .ptr
            {
            case ';':
                skipComment();  // TODO store comment in Token
                if (_includeComments)
                {
                    assert(false, "change skipComment");
                    // exprs.put(Expr(Token(TOK.comment, src[0 .. 1])));
                }
                break;
            case '(':
                exprs.put(Expr(Token(TOK.leftParen, peekNChars(1))));
                dropFront();
                ++_depth;
                break;
            case ')':
                // NOTE: this is not needed: exprs.put(Expr(Token(TOK.rightParen, src[0 .. 1])));
                dropFront();
                --_depth;
                // NOTE: this is not needed: exprs.popBack();   // pop right paren

                assert(!exprs.empty);

                // TODO retroIndexOf
                size_t count; // number of elements between parens
                while (exprs[$ - 1 - count].token.tok != TOK.leftParen)
                {
                    ++count;
                }
                assert(count != 0);

                Expr newExpr = Expr(exprs[$ - count].token,
                                    exprs[$ - count + 1 .. $].dup);
                exprs.popBackN(1 + count); // forget tokens including leftParen
                import std.algorithm : move;
                exprs.put(newExpr.move);

                if (_depth == 0) // top-level expression done
                {
                    assert(exprs.length >= 1); // we should have at least one `Expr`
                    return;
                }

                break;
            case '"':
                const stringLiteral = getStringLiteral(); // TODO tokenize
                exprs.put(Expr(Token(TOK.stringLiteral, stringLiteral)));
                break;
            case ',':
                dropFront();
                exprs.put(Expr(Token(TOK.lispComma)));
                break;
            case '`':
                dropFront();
                exprs.put(Expr(Token(TOK.lispBackQuote)));
                break;
            case '\'':
                dropFront();
                exprs.put(Expr(Token(TOK.lispQuote)));
                break;
            case '?':
                dropFront();
                const variableSymbol = getSymbol();
                exprs.put(Expr(Token(TOK.variable, variableSymbol)));
                break;
            case '@':
                dropFront();
                const variableListSymbol = getSymbol();
                exprs.put(Expr(Token(TOK.variableList, variableListSymbol)));
                break;
                // std.ascii.isDigit:
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
            case '+':
            case '-':
            case '.':
                const number = getNumber();
                exprs.put(Expr(Token(TOK.number, number)));
                break;
                // from std.ascii.isWhite
            case ' ':
            case '\t':
            case '\n':
            case '\v':
            case '\r':
            case '\f':
                assert(peekNextChar.isWhite);
                getWhitespace();
                if (_includeWhitespace)
                {
                    exprs.put(Expr(Token(TOK.whitespace, null)));
                }
                break;
            case '\0':
                assert(_depth == 0, "Unbalanced parenthesis at end of file");
                _endOfFile = true;
                return;
            default:
                // other
                if (true// src.front.isAlpha
                    )
                {
                    const symbol = getSymbol(); // TODO tokenize
                    import std.algorithm : endsWith;
                    if (symbol.endsWith(`Fn`))
                    {
                        exprs.put(Expr(Token(TOK.functionName, symbol)));
                    }
                    else
                    {
                        exprs.put(Expr(Token(TOK.symbol, symbol)));
                    }
                }
                else
                {
                    import std.conv : to;
                    assert(false,
                           `Cannot handle character '` ~ peekNextChar.to!string ~
                           `' at charater offset:` ~ _off.to!string);
                }
                break;
            }
        }
    }

private:
    size_t _off;                // current offset in `_input`
    const Src _input;           // input

    Exprs exprs;   // current

    size_t _depth;              // parenthesis depth
    bool _endOfFile;            // signals null terminator found
    bool _includeComments = false;
    bool _includeWhitespace = false;
}

@safe pure unittest
{
    const text = ";;a comment\n(instance AttrFn BinaryFunction);;another comment\0";
    auto exprs = SUOKIFParser(text);
    assert(!exprs.empty);

    assert(exprs.front.token.tok == TOK.symbol);
    assert(exprs.front.token.src == `instance`);

    assert(exprs.front.subs[0].token.tok == TOK.functionName);
    assert(exprs.front.subs[0].token.src == "AttrFn");

    assert(exprs.front.subs[1].token.tok == TOK.symbol);
    assert(exprs.front.subs[1].token.src == "BinaryFunction");
}

version(none)
unittest
{
    import std.path : expandTilde;
    import std.file : readText;
    const text = `~/elisp/mine/relangs.el`.expandTilde.readText;
    const ctext = text ~ '\0'; // null at the end to enable sentinel-based search in parser
    assert(ctext[$ - 1] == '\0');
    foreach (const ref expr; SUOKIFParser(ctext))
    {
    }
}

version = benchmark;

/** Read all SUO-KIF files (.kif) located under `rootDirPath`.
 */
version(benchmark)
unittest
{
    import std.stdio : write, writeln;
    import std.path : expandTilde;
    import std.file: dirEntries, SpanMode;

    string rootDirPath = `~/Work/sumo`;

    auto entries = dirEntries(rootDirPath.expandTilde, SpanMode.breadth, false); // false: skip symlinks
    foreach (dent; entries)
    {
        const filePath = dent.name;
        import std.algorithm : endsWith, canFind;

        import std.path : baseName, pathSplitter;

        import std.utf;
        import std.algorithm : among;
        try
        {
            if (filePath.endsWith(`.kif`) &&
                !filePath.pathSplitter.canFind(`.git`)) // invalid UTF-8 encodings
            {
                write(`Reading SUO-KIF `, filePath, ` ... `);

                import std.file : readText;
                import std.datetime : StopWatch, AutoStart, Duration;
                auto sw = StopWatch(AutoStart.yes);

                // TODO move this logic to readText(bool nullTerminated = false) by .capacity += 1
                const text = filePath.readText;
                const ctext = text ~ '\0'; // null at the end to enable sentinel-based search in parser

                foreach (const ref topExpr; SUOKIFParser(ctext))
                {
                    // TOOD use topExpr
                }
                sw.stop();
                import std.conv : to;
                writeln(`took `, sw.peek.to!Duration);
            }
        }
        catch (std.utf.UTFException e)
        {
            import std.file : read;
            writeln(" failed because of invalid UTF-8 encoding starting with ", filePath.read(16));
        }
    }
}
