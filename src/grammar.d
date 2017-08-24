/** Generic Language Constructs.
    See also: https://en.wikipedia.org/wiki/Predicate_(grammar)

    Note that ! and ? are more definite sentence enders than .

    TODO `isSomeString` => `isStringLike`
*/
module grammar;

import std.traits: isSomeChar, isSomeString;
import std.typecons: Nullable, AliasSeq;
import std.algorithm.comparison: among;
import std.algorithm: uniq, map, find, canFind, startsWith, endsWith, among;
import std.array: array;
import std.conv;

import languages: Lang;

@safe pure:

/** Computer Token Usage. */
enum Usage : ubyte
{
    unknown,
    definition,
    reference,
    call
}

/// ================ English Articles

/** English indefinite articles. */
enum englishIndefiniteArticles = [`a`, `an`];

/** English definite articles. */
enum englishDefiniteArticles = [`the`];

/** English definite articles. */
enum englishArticles = englishIndefiniteArticles ~ englishDefiniteArticles;

/** Check if $(D c) is a Vowel. */
bool isEnglishIndefiniteArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`a`, `an`); // TODO reuse englishIndefiniteArticles
}

/** Check if $(D c) is a Vowel. */
bool isEnglishDefiniteArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`the`); // TODO reuse englishDefiniteArticles
}

/** Check if $(D c) is a Vowel. */
bool isEnglishArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`a`, `an`, `the`); // TODO reuse englishArticles
}

/// ================ German Articles

/** German indefinite articles. */
enum germanIndefiniteArticles = [`ein`, `eine`, `einer`, `einem`, `eines`];

/** German definite articles. */
enum germanDefiniteArticles = [`der`, `die`, `das`, `den`, `dem`, `des`];

/** German definite articles. */
enum germanArticles = germanIndefiniteArticles ~ germanDefiniteArticles;

/** Check if $(D c) is a Vowel. */
bool isGermanIndefiniteArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`ein`, `eine`, `einer`, `einem`, `eines`); // TODO reuse germanIndefiniteArticles
}

/** Check if $(D c) is a Vowel. */
bool isGermanDefiniteArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`der`, `die`, `das`, `den`, `dem`, `des`); // TODO reuse germanDefiniteArticles
}

/** Check if $(D c) is a Vowel. */
bool isGermanArticle(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(`ein`, `eine`, `einer`, `einem`, `eines`,
                              `der`, `die`, `das`, `den`, `dem`, `des`); // TODO reuse germanArticles
}

/// ================ Vowels

/** English Vowels. */
enum englishVowels = ['a', 'o', 'u', 'e', 'i', 'y',
                      'A', 'O', 'U', 'E', 'I', 'Y'];

/** Check if $(D c) is a Vowel. */
bool isEnglishVowel(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!('a', 'o', 'u', 'e', 'i', 'y',
                              'A', 'O', 'U', 'E', 'I', 'Y'); // TODO Reuse englishVowels and hash-table
}

/** English Accented Vowels. */
enum englishAccentedVowels = ['é'];

/** Check if $(D c) is an Accented Vowel. */
bool isEnglishAccentedVowel(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!('é'); // TODO Reuse englishAccentedVowels and hash-table
}

unittest
{
    assert('é'.isEnglishAccentedVowel);
}

/** Swedish Hard Vowels. */
enum swedishHardVowels = ['a', 'o', 'u', 'å',
                          'A', 'O', 'U', 'Å'];

/** Swedish Soft Vowels. */
enum swedishSoftVowels = ['e', 'i', 'y', 'ä', 'ö',
                          'E', 'I', 'Y', 'Ä', 'Ö'];

/** Swedish Vowels. */
enum swedishVowels = (swedishHardVowels ~
                      swedishSoftVowels);

/** Check if $(D c) is a Swedish Vowel. */
bool isSwedishVowel(C)(C c)
    if (isSomeChar!C)
{
    // TODO Reuse swedishVowels and hash-table
    return cast(bool)c.among!('a', 'o', 'u', 'å', 'e', 'i', 'y', 'ä', 'ö',
                              'A', 'O', 'U', 'Å', 'E', 'I', 'Y', 'Ä', 'Ö');
}

/** Check if $(D c) is a Swedish hard vowel. */
bool isSwedishHardVowel(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!('a', 'o', 'u', 'å',
                              'A', 'O', 'U', 'Å');
}

/** Check if $(D c) is a Swedish soft vowel. */
bool isSwedishSoftVowel(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!('e', 'i', 'y', 'ä', 'ö',
                              'E', 'I', 'Y', 'Ä', 'Ö');
}

/** Spanish Accented Vowels. */
enum spanishAccentedVowels = ['á', 'é', 'í', 'ó', 'ú',
                              'Á', 'É', 'Í', 'Ó', 'Ú'];

/** Check if $(D c) is a Spanish Accented Vowel. */
bool isSpanishAccentedVowel(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(spanishAccentedVowels);
}

/** Check if $(D c) is a Spanish Vowel. */
bool isSpanishVowel(C)(C c)
    if (isSomeChar!C)
{
    return (c.isEnglishVowel ||
            c.isSpanishAccentedVowel);
}

unittest
{
    // TODO
    // assert('é'.isSpanishVowel);
}

/** Check if $(D c) is a Vowel in language $(D lang). */
bool isVowel(C)(C c, Lang lang)
    if (isSomeChar!C)
{
    switch (lang)
    {
    case Lang.en: return c.isEnglishVowel;
    case Lang.sv: return c.isSwedishVowel;
    default: return c.isEnglishVowel;
    }
}

unittest
{
    assert(!'k'.isSwedishVowel);
    assert('å'.isSwedishVowel);
}

/** English Consonants.
    See also: https://simple.wikipedia.org/wiki/Consonant
*/
enum EnglishConsonant { b, c, d, f, g, h, j, k, l, m, n, p, q, r, s, t, v, w, x }

/** English Consontants. */
enum englishConsonants = ['b', 'c', 'd', 'f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't', 'v', 'w', 'x',
                          'B', 'C', 'D', 'F', 'G', 'H', 'J', 'K', 'L', 'M', 'N', 'P', 'Q', 'R', 'S', 'T', 'V', 'W', 'X'];

/** Check if $(D c) is a Consonant. */
bool isEnglishConsonant(C)(C c)
    if (isSomeChar!C)
{
    // TODO Reuse englishConsonants and hash-table
    return cast(bool)c.among!('b', 'c', 'd', 'f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't', 'v', 'w', 'x',
                              'B', 'C', 'D', 'F', 'G', 'H', 'J', 'K', 'L', 'M', 'N', 'P', 'Q', 'R', 'S', 'T', 'V', 'W', 'X');
}
alias isSwedishConsonant = isEnglishConsonant;

unittest
{
    // TODO
    // assert('k'.isEnglishConsonant);
    // assert(!'å'.isEnglishConsonant);
}

/** English Letters. */
enum englishLetters = englishVowels ~ englishConsonants;

/** Check if $(D c) is a Letter. */
bool isEnglishLetter(C)(C c)
    if (isSomeChar!C)
{
    return cast(bool)c.among!(englishLetters);
}
alias isEnglish = isEnglishLetter;

unittest
{
    // TODO
    // assert('k'.isEnglishLetter);
    // assert(!'å'.isEnglishLetter);
}

enum englishDoubleConsonants = [`bb`, `dd`, `ff`, `gg`, `mm`, `nn`, `pp`, `rr`, `tt`, `ck`, `ft`];

/** Check if $(D c) is an English Double consonant. */
bool isEnglishDoubleConsonant(S)(S s)
    if (isSomeString!S)
{
    return cast(bool)c.among!(`bb`, `dd`, `ff`, `gg`, `mm`, `nn`, `pp`, `rr`, `tt`, `ck`, `ft`);
}

/** Computer token. */
enum TokenId : ubyte
{
    unknown,

    keyword,
    type,
    constant,
    comment,
    variableName,
    functionName,
    builtinName,
    templateName,
    macroName,
    aliasName,
    enumeration,
    enumerator,
    constructor,
    destructors,
    operator,
}

/** Verb Form. */
enum VerbForm : ubyte
{
    unknown,

    imperative,
    infinitive, base = infinitive, // sv:infinitiv,grundform
    present, // sv:presens
    past, preteritum = past, // sv:imperfekt
    supinum, pastParticiple = supinum,
}

/** Verb Instance. */
struct Verb(S)
    if (isSomeString!S)
{
    S expr;
    VerbForm form;
    alias expr this;
}

/** Subject Count. */
enum Count : ubyte
{
    unknown,
    singular,
    plural,
    uncountable
}

struct Noun(S)
    if (isSomeString!S)
{
    S expr;
    Count count;
    alias expr this;
}

/** Comparation.
    See also: https://en.wikipedia.org/wiki/Comparison_(grammar)
*/
enum Comparation : ubyte
{
    unknown,
    positive,
    comparative,
    superlative,
    elative,
    exzessive
}

struct Adjective(S)
    if (isSomeString!S)
{
    S expr;
    Comparation comparation;
    alias expr this;
}

/** English Tense.
    Tempus on Swedish.
    See also: http://www.ego4u.com/en/cram-up/grammar/tenses-graphic
    See also: http://www.ego4u.com/en/cram-up/grammar/tenses-examples
*/
enum Tense : ubyte
{
    unknown,

    present, presens = present, // sv:nutid
    past, preteritum = past, imperfekt = past, // sv:dåtid, https://en.wikipedia.org/wiki/Past_tense
    future, futurum = future, // framtid, https://en.wikipedia.org/wiki/Future_tense

    pastMoment,
    presentMoment, // sv:plays
    futureMoment, // [will|is going to|intends to] play

    pastPeriod,
    presentPeriod,
    futurePeriod,

    pastResult,
    presentResult,
    futureResult,

    pastDuration,
    presentDuration,
    futureDuration,
}
alias Tempus = Tense;

nothrow @nogc
{
    bool isPast(Tense tense)
    {
        with (Tense)
            return cast(bool)tense.among!(past, pastMoment, pastPeriod, pastResult, pastDuration);
    }

    bool isPresent(Tense tense)
    {
        with (Tense)
            return cast(bool)tense.among!(present, presentMoment, presentPeriod, presentResult, presentDuration);
    }

    bool isFuture(Tense tense)
    {
        with (Tense)
            return cast(bool)tense.among!(future, futureMoment, futurePeriod, futureResult, futureDuration);
    }
}

/** Part of a Sentence. */
enum SentencePart : ubyte
{
    unknown,
    subject,
    predicate,
    adverbial,
    object,
}

enum Adverbial
{
    unknown,

    manner,          // they were playing `happily` (sätts-adverbial in Swedish)

    place,                      // we met in `London`, `at the beach`
    space = place,

    time,                       // they start work `at six thirty`

    probability,                // `perhaps` the weather will be fine

    direction, // superman flew `in`, the car drove `out` (förändring av tillstånd in Swedish)
    location,  // are you `in`?, the ball is `out` (oföränderligt tillstånd in Swedish)

    quantifier,                 // he weighs `63 kilograms` (måtts-adverbial in Swedish)

    comparation,                // (grads-adverbial in Swedish)

    cause,                      // (orsaks-adverbial in Swedish)

    circumstance,               // (omständighets-adverbial in Swedish)
}

class Part
{
}

class Predicate : Part
{
}

// TODO: Conversion to Sense
enum Article : ubyte
{
    unknown,
    indefinite,
    definite,
    partitive
}

class Subject : Part
{
    Article article;
}

static immutable implies = [`in order to`];

/** Subject Person. */
enum Person : ubyte { unknown, first, second, third }

/** Subject Gender. */
enum Gender : ubyte
{
    unknown,
    male, maskulinum = male,
    female, femininum = female,
    neutral, neuter = neutral, neutrum = neuter, // non-alive. for example: "något"
    common, utrum = common, reale = utrum, // real/alive. for example: "någon"
}

/** (Grammatical) Mood.
    Sometimes also called Mode.
    Modus in Swedish.
    See also: https://en.wikipedia.org/wiki/Grammatical_mood
*/
enum Mood : ubyte
{
    unknown,
    indicative, // indikativ in Swedish. Example: I eat pizza.
    subjunctive, // TODO: if I were to eat more pizza I would be sick.
    conjunctive = subjunctive, // konjunktiv in Swedish
    conditional,
    optative,
    imperative, // imperativ in Swedish. Example: eat the pizza!
    jussive,
    potential,
    inferential,
    interrogative,
    whQuestion, // TODO make alias? Example: who is eating pizza?
    ynQuestion, // TODO make alias? Example: did you eat pizza?
}

/** Check if $(D mood) is a Realis Mood.
    See also: https://en.wikipedia.org/wiki/Grammatical_mood#Realis_moods
 */
bool isRealis(Mood mood) @nogc nothrow
{
    with (Mood)
        return cast(bool)mood.among!(indicative);
}

enum realisMoods = [Mood.indicative];

/** Check if $(D mood) is a Irrealis Mood.
    See also: https://en.wikipedia.org/wiki/Grammatical_mood#Irrealis_moods
*/
bool isIrrealis(Mood mood) @nogc nothrow
{
    with (Mood)
        return cast(bool)mood.among!(subjunctive,
                                     conditional,
                                     optative,
                                     imperative,
                                     jussive,
                                     potential,
                                     inferential);
}

enum irrealisMoods = [Mood.subjunctive,
                      Mood.conditional,
                      Mood.optative,
                      Mood.imperative,
                      Mood.jussive,
                      Mood.potential,
                      Mood.inferential];

/** English Negation Prefixes.
    See also: http://www.english-for-students.com/Negative-Prefixes.html
*/
static immutable englishNegationPrefixes = [ `un`, `non`, `dis`, `im`, `in`, `il`, `ir`, ];

static immutable swedishNegationPrefixes = [ `icke`, `o`, ];

/** English Noun Suffixes.
    See also: http://www.english-for-students.com/Noun-Suffixes.html
 */
static immutable adjectiveNounSuffixes = [ `ness`, `ity`, `ment`, `ance` ];
static immutable verbNounSuffixes = [ `tion`, `sion`, `ment`, `ence` ];
static immutable nounNounSuffixes = [ `ship`, `hood` ];
static immutable allNounSuffixes = (adjectiveNounSuffixes ~
                                    verbNounSuffixes ~
                                    nounNounSuffixes ~
                                    [ `s`, `ses`, `xes`, `zes`, `ches`, `shes`, `men`, `ies`, ]);

/** English Verb Suffixes. */
static immutable verbSuffixes = [ `s`, `ies`, `es`, `es`, `ed`, `ed`, `ing`, `ing`, ];

/** English Adjective Suffixes. */
static immutable adjectiveSuffixes = [ `er`, `est`, `er`, `est` ];

/** English Job/Professin Title Suffixes.
    Typically built from noun or verb bases.
    See also: http://www.english-for-students.com/Job-Title-Suffixes.html
*/
static immutable jobTitleSuffixes = [ `or`, // traitor
                                      `er`, // builder
                                      `ist`, // typist
                                      `an`, // technician
                                      `man`, // dustman, barman
                                      `woman`, // policewoman
                                      `ian`, // optician
                                      `person`, // chairperson
                                      `sperson`, // spokesperson
                                      `ess`, // waitress
                                      `ive` // representative
    ];

/** English Linking Verbs in Nominative Form.
 */
static immutable englishLinkingVerbs = [`is`, `seem`, `look`, `appear to be`, `could be`];
static immutable swedishLinkingVerbs = [`är`, `verkar`, `ser`, `kan vara`];

/** English Word Suffixes. */
static immutable wordSuffixes = [ allNounSuffixes ~ verbSuffixes ~ adjectiveSuffixes ].uniq.array;

/** Return string $(D word) in plural optionally in $(D count). */
string inPlural(string word, int count = 2,
                string pluralWord = null)
{
    if (count == 1 || word.length == 0)
    {
        return word; // it isn't actually inPlural
    }
    if (pluralWord !is null)
    {
        return pluralWord;
    }
    switch (word[$ - 1])
    {
        case 's':
        case 'a', 'e', 'i', 'o', 'u':
            return word ~ `es`;
        case 'f':
            return word[0 .. $-1] ~ `ves`;
        case 'y':
            return word[0 .. $-1] ~ `ies`;
        default:
            return word ~ `s`;
    }
}

/** Return $(D s) lemmatized (normalized).
    See also: https://en.wikipedia.org/wiki/Lemmatisation
 */
S lemmatized(S)(S s) nothrow
    if (isSomeString!S)
{
    if      (s.among!(`be`, `is`, `am`, `are`)) return `be`;
    else if (s.among!(`do`, `does`))            return `do`;
    else return s;
}

/**
   TODO Reuse knet translation query instead.
 */
string negationIn(Lang lang) nothrow @nogc
{
    switch (lang) with (Lang)
    {
    case en: return `not`;
    case sv: return `inte`;
    case de: return `nicht`;
    default: return `not`;
    }
}

enum Manner : ubyte
{
    formal,
    informal,
    slang,
    rude,
}

/** Grammatical Case.
    See also: https://en.wikipedia.org/wiki/Grammatical_case
*/
enum Case : ubyte
{
    unknown,
    nominative,
    genitive,
    dative,
    accusative,
    ablative
}

/** English Subject Pronouns.
   See also: https://en.wikipedia.org/wiki/Subject_pronoun
*/
enum englishSubjectPronouns = [`I`,
                               `you`,
                               `he`, `she`, `it`,
                               `we`,
                               `they`,
                               `what`,
                               `who`];

/** Swedish Subject Pronouns.
    See also: https://en.wikipedia.org/wiki/Subject_pronoun
*/
enum swedishSubjectPronouns = [`jag`, `du`,
                               `han`, `hon`, `den`, `det`,
                               `vi`,
                               `de`,
                               `vad`,
                               `vem`];

/** English Object Pronouns.
    See also: https://en.wikipedia.org/wiki/Object_pronoun
*/
enum englishObjectPronouns = [`me`,
                              `him,`, `her`,
                              `us`,
                              `them`,
                              `whom`];

/** Swedish Object Pronouns.
    See also: https://en.wikipedia.org/wiki/Object_pronoun
*/
enum swedishObjectPronouns = [`mig`,
                              `honom,`, `henne`,
                              `oss`,
                              `dem`];

/// Indefinite article of `s` in language `lang`.
string indefiniteArticleIn(string s, Lang lang)
    /*nothrow @nogc*/
{
    import std.range.primitives : empty, front;
    return (!s.empty && s.front.isVowel(lang) ? `an` : `a`);
}

/// Definite article of `s` in language `lang`.
string definiteArticleIn(string s, Lang lang)
    /*/*nothrow @nogc*/
{
    switch (lang)
    {
    case Lang.en:
    default:
        return `the`;
    }
}

auto inIndefiniteNounForm(string s, Lang lang)
    /*nothrow @nogc*/
{
    import std.range : chain;
    return chain(s.indefiniteArticleIn(lang), ` `, s);
}

/*nothrow @nogc*/ unittest
{
    import std.algorithm : equal;
    assert(equal(`person`.inIndefiniteNounForm(Lang.en),
                 `a person`));
    assert(equal(`apple`.inIndefiniteNounForm(Lang.en),
                 `an apple`));
}

auto inDefiniteNounForm(string s, Lang lang)
{
    import std.range : chain;
    return chain(s.definiteArticleIn(lang), ` `, s);
}

enum Casing
{
    unknown,
    lower,
    upper,
    capitalized,
    camel
}
