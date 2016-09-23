/** SUO-KIF File Format. */
module suokif;

// import std.range : isInputRange;

enum Token
{
    leftParen,
    rightParen,
    symbol,
    stringLiteral,
    infers,
    and_,
    or_,
    exists_,
    not_,
    variable,
}

import array_ex : Array;

/** Parse SUO-KIF from `src`. */
Array!Token parseSUOKIF(string src) @safe pure
{
    import std.range : empty, front, popFront;
    import std.uni : isWhite, isAlpha;
    import std.ascii : isDigit;
    import std.algorithm : among, skipOver;
    import dbgio : dln;

    typeof(return) tokens;

    const whole = src;

    src.skipOver(x"EFBBBF");    // skip magic? header for some files

    /// Skip comment.
    void skipComment()
    {
        while (!src.empty && !src.front.among('\r', '\n')) // until end of line
        {
            src.popFront();
        }
    }

    /// Get symbol.
    string getSymbol()
    {
        size_t i = 0;
        while (i != src.length && src[i].isAlpha) { ++i; }
        const symbol = src[0 .. i]; src = src[i .. $]; // TODO functionize
        return symbol;
    }

    /// Get numeric literal (number).
    string getNumber()
    {
        size_t i = 0;
        while (i != src.length && src[i].isDigit) { ++i; }
        const number = src[0 .. i]; src = src[i .. $]; // TODO functionize
        return number;
    }

    /// Get string literal.
    string getStringLiteral()
    {
        src.popFront();         // pop leading double quote
        size_t i = 0;
        while (i != src.length && src[i] != '"') { ++i; }
        const literal = src[0 .. i]; src = src[i .. $]; // TODO functionize
        src.popFront();         // pop ending double quote
        return literal;
    }

    /// Skip whitespace.
    string getWhitespace()
    {
        size_t i = 0;
        while (i != src.length && src[i].isWhite) { ++i; }
        const whitespace = src[0 .. i]; src = src[i .. $]; // TODO functionize
        return whitespace;
    }

    while (!src.empty)
    {
        // dlnl("front:'", src.front, "'");
        if (src.front == ';')
        {
            skipComment();
        }
        else if (src.front == '(')
        {
            tokens ~= Token.leftParen;
            src.popFront();
        }
        else if (src.front == ')')
        {
            tokens ~= Token.rightParen;
            src.popFront();
        }
        else if (src.front == '"')
        {
            const stringLiteral = getStringLiteral(); // TODO tokenize
        }
        else if (src.front == '=')
        {
            src.popFront();
            if (src.front == '>')
            {
                tokens ~= Token.infers;
                src.popFront();
            }
            else
            {
                assert(false);
            }
        }
        else if (src.front == '?')
        {
            src.popFront();
            const variableSymbol = getSymbol(); // TODO tokenize
        }
        else if (src.front.isWhite)
        {
            getWhitespace();
        }
        else if (src.front.isAlpha)
        {
            const symbol = getSymbol(); // TODO tokenize
        }
        else if (src.front.isDigit)
        {
            const number = getNumber(); // TODO tokenize
        }
        else if (src.skipOver(`and`)) { tokens ~= Token.and_; }
        else if (src.skipOver(`or`)) { tokens ~= Token.or_; }
        else if (src.skipOver(`exists`)) { tokens ~= Token.exists_; }
        else if (src.skipOver(`not`)) { tokens ~= Token.not_; }
        else { assert(false); }
    }

    return tokens;
}

// void lexSUOKIF(R)(R src)
// {
//     import std.experimental.lexer;

//     static immutable TokOperators = [ "(", ")", "=>" ];
//     static immutable TokDynamic = [ "stringLiteral", "comment", "identifier", "numberLiteral", "whitespace" ];
//     static immutable TokKeywords = [ "and", "exists", "or", "not" ];
//     import std.meta : AliasSeq;

//     alias Toks = AliasSeq!(TokOperators, TokDynamic, TokKeywords);
//     alias TokID = TokenIdType!Toks;
//     alias tokToString = tokenStringRepresentation!(TokID, Toks);
//     alias tok(string symbol) = TokenId!(TokID, LuaTokens, symbol);

//     static immutable tokenHandlers = [
//         "\"", "lexStringLiteral",
//         ";", "lexComment",
//         " ",  "lexWhitespace",
//         "\t", "lexWhitespace",
//         "\r", "lexWhitespace",
//         "\n", "lexWhitespace",
//         ];
// }

unittest
{
    import std.path : expandTilde;
    const file = "~/Work/justd/phobos-next/src/emotion.kif".expandTilde;

    import std.file : readText;
    // file.readText.lexSUOKIF();
    file.readText.parseSUOKIF();
}
