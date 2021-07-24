/**
 * The demangle module converts mangled D symbols to a representation similar
 * to what would have existed in code.
 *
 * Copyright: Copyright Sean Kelly 2010 - 2014.
 * License: Distributed under the
 *      $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0).
 *    (See accompanying file LICENSE)
 * Authors:   Sean Kelly
 * Source:    $(DRUNTIMESRC corex/_demangle.d)
 */

module corex.demangle;

version (OSX)
    version = Darwin;
else version (iOS)
    version = Darwin;
else version (TVOS)
    version = Darwin;
else version (WatchOS)
    version = Darwin;

debug(trace) import core.stdc.stdio : printf;
debug(info) import core.stdc.stdio : printf;

private struct Demangler {
nothrow pure @safe:

    /**
     * Constructs a Demangler with an input buffer and optional destination
     * buffer
     *
     * Params:
     *   buf = mangled data
     *   dst = destination buffer for the demangled data
     */
    this(return const(char)[] buf, return char[] dst)
    {
        buffer = BufferRange(buf);
        data = Data(dst);
    }

    /**
     * Do the demangle proccess
     * Returns: return demangled name
     */
    char[] doDemangle()
    {
        debug(trace) {
            bool ret = parseMangledName();
            printf("doDemangle buffer=%s data=%s\n", (buffer.buf ~ '\0').ptr, (data.arr ~ '\0').ptr);
            return ret ? data.arr : buffer.buf.dup;
        }
        else return parseMangledName() ? data.arr : buffer.buf.dup;
    }

private:


    /**
     * Represents a result of a parser
     */
    struct Result(T)
    {
        this(U)(Result!U value)
        if(!is(U == T))
        {
            if (value) hasValue = true;

            static if (!is(T == void))
            {
                if (value) res = T.init;
            }
        }

        static if (!is(T == void))
        {
            this(T value)
            {
                hasValue = true;
                res = value;
            }

            T get()
                in(hasValue)
            {
                return res;
            }


            private T res = void;
        }
        else
        {
            this(bool hasValue)
            {
                this.hasValue = hasValue;
            }

            alias hasValue this;
        }

        bool success() const @property { return hasValue; }
        bool opCast() const { return hasValue; }

        private bool hasValue;
    }

    // syntax sugar to infer T of a Result!T
    static Result!T result(T)(T value) { return Result!(T)(value); }
    static Result!T result(T)(bool hasValue) if(is(T == void)) { return Result!(T)(hasValue); }
    static Result!T result(T)(ParserFlags pf) if(is(T == void)) { return Result!(T)(cast(bool)pf); }
    static Result!T result(T)() { return Result!(T).init; }
    static Result!T result(T)(T value, ParserFlags pf) { return result!T(value, cast(bool) pf); }
    static Result!T result(T)(T value, bool hasValue)
    {
        return (hasValue)
            ? Result!T(value)
            : Result!T();
    }

    // syntax sugar for success results
    static Result!void success()() { return Result!void(true); }
    static Result!T success(T)(T value) { return result(value); }
    static Result!T success(T)(Result!T retValue) { return retValue; }

    // syntax sugar for failed results
    static Result!void fail()() { return Result!void(false); }
    static auto fail(T)()
    {
        static if (is(T == Result!Args, Args...))
            return T();
        else
            return Result!T();
    }

    //////////////////////////////////////////////////////////////////////////
    // Parsing Implementation
    //////////////////////////////////////////////////////////////////////////

    enum ParserFlags : uint
    {
        None              = 0,    /// No parser flags passed
        EarlyIsParse      = 1<<0, /// Perform parsing in is<Node> functions
        EarlyNumberDecode = 1<<1, /// Number already decoded, implies TemplateNumber
        TemplateNumber    = 1<<2, /// Template number length is provided
        EarlyTemplateID   = 1<<3, /// Template ID partially parsed
        Optional          = 1<<4, /// Whether it's an optional parsing stage
        TFunctionDelegate = 1<<5, /// A delegate function type is being parsed
        OverrideData      = 1<<6, /// Override data on write
        Silent            = 1<<7, /// Don't increment length of the data buffer
        Propagate         = 1<<8, /// Propagate flags to child calls
    }

    // code inside every parser call
    template initParser(string func = __FUNCTION__)
    {
        //TODO: remove if buffer.empty and call it only when needed
        enum printfFormatter = ` pf=0x%08x front=%c pos=%zu\n", cast(uint)pf, buffer.empty ? '\0' : buffer.front, buffer.pos);`;
        enum initParser = q{if (buffer.empty) return typeof(return)(fail()); } ~
            `debug(trace) printf("+ ` ~
                func ~
                printfFormatter ~
            `debug(trace) scope(exit) printf("- ` ~
                func ~
                printfFormatter ~
            q{enum ParserFlags ppf = (pf & ParserFlags.Propagate) ? pf : ParserFlags.None;};
    }

    enum notImplementedParser = q{
        debug(trace) printf("!!! Not yet implemented!\n");
        return typeof(return)(fail());
    };

    /*
    MangledName:
        _D QualifiedName Type
        _D QualifiedName Z
    */
    Result!void parseMangledName(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        if(!buffer.match("_D") || !parseQualifiedName())
            return fail();

        if(buffer.match('Z'))
        {
            /*
            Matching internal symbol
            This 'type' is used for untyped internal symbols, i.e.:
              - __array
              - __init
              - __vtbl
              - __Class
              - __Interface
              - __ModuleInfo
              */
             return success();
        }
        else
        {
            // match first option
            auto parseRes = parseType();
            if(!parseRes) return fail();
            //FIXME: prepend is not the way here
            data.prepend(' ');
            data.prepend!(ParserFlags.OverrideData)(parseRes.get());
            return success();
        }
    }

    /*
    QualifiedName:
        SymbolFunctionName
        SymbolFunctionName QualifiedName
    */
    Result!void parseQualifiedName(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        size_t n;

        do {
            if(n++) data ~= '.';
            if(!parseSymbolFunctionName())
                return fail();
        } while(isSymbolFunctionNameFront());

        return success();
    }

    /*
    SymbolFunctionName:
        SymbolName
        SymbolName TypeFunctionNoReturn
        SymbolName M TypeModifiers(opt) TypeFunctionNoReturn
    */
    Result!void parseSymbolFunctionName(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        // error matching SymbolFunctionName
        if(!parseSymbolName()) return fail();

        if(isTypeFunctionNoReturnFront())
        {
            // match second option
            return parseTypeFunctionNoReturn();
        }
        else
        {
            // match first option
            if(!buffer.match('M')) return success();

            // match third option
            if(!parseTypeModifiers!(ParserFlags.Optional)) return fail();
            return parseTypeFunctionNoReturn();
        }
    }

    /*
    TypeModifiers:
        Const
        Wild
        Wild Const
        Shared
        Shared Const
        Shared Wild
        Shared Wild Const
        Immutable
    */
    Result!void parseTypeModifiers(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        if(buffer.empty)
            return result!void(pf & ParserFlags.Optional);

        switch(buffer.front)
        {
            case 'y': // Immutable
                buffer.popFront();
                data ~= "immutable ";
                break;

            case 'O': // Shared
                buffer.popFront();
                data ~= "shared ";

                if (buffer.front == 'x')
                    goto case 'x';
                if (buffer.front == 'N')
                    goto case 'N';

                break;

            case 'x': // Const
                buffer.popFront();
                data ~= "const ";
                break;

            case 'N': // Wild
                if (buffer.peek(1) != 'g')
                    return fail();

                buffer.popFront();
                buffer.popFront();
                data ~= "inout ";

                if (buffer.front == 'x')
                    goto case 'x';

                break;

            default:
                return result!void(pf & ParserFlags.Optional);
        }
        return success();
    }

    /*
    SymbolName:
        LName
        TemplateInstanceName
        IdentifierBackRef
        0                         // anonymous symbols
    */
    Result!void parseSymbolName(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        switch(buffer.front)
        {
            // for anonymous symbols
            case '0':
                buffer.popFront();
                data ~= "__anonymous";
                return success();
            // match second option
            case '_': return parseTemplateInstanceName();
            // match first option or second option in case of backward
            // compatible ABI
            case '1': .. case '9':
            {
                // Usage of early number decode for backward compatibility with
                // template instances
                auto ret = decodeNumber();
                if(!ret.success()) return fail();

                // Early check empty buffer for no range violation in the printf
                // trace logging
                debug(trace) if(buffer.empty) return fail();

                {
                    auto begPos = buffer.pos;
                    if(isTemplateIDFront!(ParserFlags.EarlyIsParse))
                        // Early parse TemplateID partially
                        return parseTemplateInstanceName!(
                                ParserFlags.TemplateNumber |
                                ParserFlags.EarlyTemplateID |
                                ParserFlags.EarlyNumberDecode
                                )(ret.get(), begPos);
                }

                return parseLName!(ParserFlags.EarlyNumberDecode)(ret.get());
            }
            // match third option
            case 'Q':
                return parseLNameBackRef();
            default:
                return fail();
        }
    }

    Result!void parseLNameBackRef(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        auto refPos = buffer.pos;
        buffer.popFront();

        auto retb = decodeBackref();
        // on error or invalid back reference
        if(retb.error || !retb.value || retb.value > refPos) return fail();

        // save position to restore
        auto savePos = buffer.pos;
        buffer.pos = refPos - retb.value;

        bool ret;
        switch(buffer.front)
        {
            case 'Q':
                ret = parseLNameBackRef();
                break;
            default:
                ret = parseLName();
                break;
        }
        buffer.pos = savePos;
        return result!void(ret);
    }


    /*
    LName:
        Number Name

    Number:
        Digit
        Digit Number

    Digit:
        0
        1
        2
        3
        4
        5
        6
        7
        8
        9
    */
    Result!void parseLName(ParserFlags pf = ParserFlags.None)(size_t decodedNum = size_t.init)
    {
        mixin(initParser!());

        if(buffer.empty) return fail();

        static if (pf == ParserFlags.EarlyNumberDecode)
            // A Number already got parsed earlier
            immutable n = decodedNum;
        else
        {
            auto ret = decodeNumber();
            if(!ret.success()) return fail();

            immutable n = ret.get();
        }

        if (n > buffer.buf.length || n > buffer.buf.length - buffer.pos)
           // LName must be at least 1 character
           return fail();

        if ('_' != buffer.front && !isAlpha(buffer.front))
           // Invalid character in LName
           return fail();

        foreach (char e; buffer.buf[buffer.pos + 1 .. buffer.pos + n])
        {
           if ('_' != e && !isAlpha(e) && !isDigit(e))
               return fail();
       }

        data ~= buffer.buf[buffer.pos .. buffer.pos + n];
        buffer.pos += n;
        return success();
    }

    /*
    TypeFunctionNoReturn:
        CallConvention FuncAttrs(opt) Parameters(opt) ParamClose
    */
    Result!void parseTypeFunctionNoReturn(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        if(!parseCallConvention()) return fail();

        // optional
        auto begPos = data.arr.length;
        if(!parseFuncAttrs!(ParserFlags.Optional)) return fail();

        auto endPos = data.arr.length;
        data ~= '(';
        // parse function parameters
        if(!parseParameters!(ParserFlags.Optional)) return fail();
        if(!parseParamClose()) return fail();
        data ~= ')';
        if(endPos - begPos)
        {
            data.shiftEnd(endPos-1 , endPos);
            data.shiftEnd(begPos, endPos-1);
        }

        return success();
    }

    /*
    FuncAttrs:
        FuncAttr
        FuncAttr FuncAttrs

    FuncAttr:
        FuncAttrPure
        FuncAttrNothrow
        FuncAttrRef
        FuncAttrProperty
        FuncAttrNogc
        FuncAttrReturn
        FuncAttrScope
        FuncAttrTrusted
        FuncAttrSafe
        FuncAttrLive
    */
    Result!void parseFuncAttrs(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        if(buffer.front != 'N') return result!void(pf & ParserFlags.Optional);

        do
        {
            buffer.popFront();
            switch(buffer.front)
            {
                case 'a': // pure
                    buffer.popFront();
                    data ~= "pure ";
                    continue;
                case 'b': // nothrow
                    buffer.popFront();
                    data ~= "nothrow ";
                    continue;
                case 'c': // ref
                    buffer.popFront();
                    data ~= "ref ";
                    continue;
                case 'd': // @property
                    buffer.popFront();
                    data ~= "@property ";
                    continue;
                case 'e': // @trusted
                    buffer.popFront();
                    data ~= "@trusted ";
                    continue;
                case 'f': // @safe
                    buffer.popFront();
                    data ~= "@safe ";
                    continue;
                case 'g':
                case 'h':
                case 'k':
                    // NOTE: The inout parameter type is represented as "Ng".
                    //       The vector parameter type is represented as "Nh".
                    //       The return parameter type is represented as "Nk".
                    //       These make it look like a FuncAttr, but infact if
                    //       we see these, then we know we're really in the
                    //       parameter list.  Rewind and break.
                    --buffer.pos;
                    debug(trace) printf("Going back with N\n");
                    return success();
                case 'i': // @nogc
                    buffer.popFront();
                    data ~= "@nogc ";
                    continue;
                case 'j': // return
                    buffer.popFront();
                    data ~= "return ";
                    continue;
                case 'l': // scope
                    buffer.popFront();
                    data ~= "scope ";
                    continue;
                case 'm': // @live
                    buffer.popFront();
                    data ~= "@live ";
                    continue;

                default: return fail();
            }
        } while(buffer.front == 'N');

        return success();
    }

    /*
    Parameters:
        Parameter
        Parameter Parameters

    Parameter:
        Parameter2
        M Parameter2     // scope
        Nk Parameter2    // return
    */
    Result!void parseParameters(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        bool opt = cast(bool)(pf & ParserFlags.Optional);

        for(size_t n; ; n++)
        {
            debug(trace) printf("Parameter %d\n", n);
            // exit or append the comma
            switch(buffer.front)
            {
                case 'X': .. case 'Z':
                    return result!void(opt);
                default: if(n) data ~= ", ";
            }

            // surely a parameter otherwise fail
            switch(buffer.front)
            {
                case 'M': // scope
                    buffer.popFront();
                    data ~= "scope ";
                    if(!parseParameter2()) return fail();
                    break;
                case 'N': // maybe? return otherwise parseType()
                    buffer.popFront();
                    if ('k' == buffer.front)
                    {
                        buffer.popFront();
                        data ~= "return ";
                    } else {
                        // it can be Type
                        buffer.pos--;
                    }
                    break;

                default: break;
            }

            if(!parseParameter2()) return fail();

            // make it optional now
            opt = true;
        }
    }

    /*
    Parameter2:
        Type
        I Type     // in
        J Type     // out
        K Type     // ref
        L Type     // lazy
    */
    Result!void parseParameter2(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        switch(buffer.front)
        {
            case 'I': // in
                buffer.popFront();
                data ~= "in ";
                if (buffer.front == 'K')
                {
                    /*
                    Currently `in ref` is valid. When `-preview=in` is passed
                    to the compiler, `in ref` is an error, but the compiler will
                    still encode in where ref is used as in ref (to avoid
                    mismatches in ABI). This explains why is not specified on
                    the ABI grammar.
                    */

                    goto case 'K';
                }
                break;
            case 'J': // out
                buffer.popFront();
                data ~= "out ";
                break;
            case 'K': // ref
                buffer.popFront();
                data ~= "ref ";
                break;
            case 'L': // lazy
                buffer.popFront();
                data ~= "lazy ";
                break;

            default: break;
        }

        return typeof(return)(parseType());
    }

    /*
    ParamClose
        X     // variadic T t...) style
        Y     // variadic T t,...) style
        Z     // not variadic
    */
    Result!void parseParamClose(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        switch(buffer.front)
        {
            case 'X': // variadic T t...) style
                buffer.popFront();
                data ~= "...";
                return success();
            case 'Y': // variadic T t,...) style
                buffer.popFront();
                data ~= ", ...";
                return success();
            case 'Z': // not variadic
                buffer.popFront();
                return success();

            // error
            default: return fail();
        }
    }

    /*
    CallConvention:
        F       // D
        U       // C
        W       // Windows
        R       // C++
        Y       // Objective-C
    */
    Result!void parseCallConvention(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        switch(buffer.front)
        {
            case 'F': // D
                buffer.popFront();
                return success();
            case 'U': // C
                buffer.popFront();
                data ~= "extern(C) ";
                return success();
            case 'W': // Windows
                buffer.popFront();
                data ~= "extern(Windows) ";
                return success();
            case 'R': // C++
                buffer.popFront();
                data ~= "extern(C++) ";
                return success();
            case 'Y': // Objective-C
                buffer.popFront();
                data ~= "extern (Objective-C) ";
                return success();

            // error
            default: return fail();
        }
    }

    //TODO: Add documentation
    Result!void parseTemplateInstanceName(ParserFlags pf = ParserFlags.None)
        (size_t decodedNum = size_t.init, size_t tidPos = size_t.init)
    {
        mixin(initParser!());

        static if (pf & ParserFlags.EarlyNumberDecode) // implies TemplateInstanceNumber.yes
        {
            immutable n = decodedNum;
            if(n == 0) return fail();
        }

        static if (!(pf & ParserFlags.EarlyTemplateID))
        {
            // check for backward compatible ABI
            static if ((pf & ParserFlags.TemplateNumber) && !(pf & ParserFlags.EarlyNumberDecode))
            {
                auto ret = decodeNumber();
                if(!ret.success()) return fail();

                immutable n = ret.get();
            }

            // save position to validate number of chars afterwards
            static if (pf & ParserFlags.TemplateNumber)
                immutable begPos = buffer.pos;

            if(!buffer.match("__")) return fail();
        }

        // use saved position
        static if ((pf & ParserFlags.EarlyTemplateID) && (pf & ParserFlags.TemplateNumber))
            immutable begPos = tidPos;

        if(buffer.empty) return fail();
        switch(buffer.front)
        {
            case 'T':
            case 'U':
                buffer.popFront();
                parseLName();
                data ~= "!(";
                if(!parseTemplateArgs()) return fail();
                if(!buffer.match('Z')) return fail();

                // check if saved position has a correspoding valid length
                static if (pf & ParserFlags.TemplateNumber)
                {
                    debug(trace) printf("parseTemplateInstanceName::checkNumber beg=%lu end=%lu n=%lu\n", begPos, buffer.pos, n);
                    if (buffer.pos - begPos != n) return fail();
                }

                data ~= ")";
                return success();
            default: break;
        }

        return fail();
    }

    /*
    TemplateArgs:
        TemplateArg
        TemplateArg TemplateArgs
    TemplateArg:
        TemplateArgX
        H TemplateArgX
    TemplateArgX:
        T Type
        V Type Value
        S Number_opt QualifiedName
        X ExternallyMangledName
    */
    Result!void parseTemplateArgs(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        for (size_t n = 0; ; n++)
        {
            // skip specialized template parameters
            if (buffer.front == 'H')
                buffer.popFront();

            void handleArg()
            {
                buffer.popFront();
                if(n) data ~= ", ";
            }

            switch(buffer.front)
            {
                case 'T':
                    handleArg();
                    parseType();
                    continue;
                case 'V':
                    handleArg();

                    char t = buffer.front;
                    // check for back reference
                    if (t == 'Q')
                    {
                        auto ret = peekBackref();
                        if(ret.error) return fail();
                        t = ret.value;
                    }
                    auto name = parseType!(ParserFlags.Silent)();
                    if(!name) return fail();
                    if(!parseValue(name.get(), t)) return fail();
                    continue;

                default: return success();
            }
        }
    }

    Result!void parseValue(ParserFlags pf = ParserFlags.None)(scope const(char)[] name = null, char type = '\0')
    {
        mixin(initParser!());

        switch(buffer.front)
        {
            case 'n': // null value
                buffer.popFront();
                data ~= "null";
                return success();

            case 'i': // integer literal
                buffer.popFront();
                if ('0' > buffer.front || '9' < buffer.front)
                    return fail();
                goto case;
            case '0': .. case '9':
                return parseIntegerValue(type);

            case 'N': // negative integer literal
                buffer.popFront();
                data ~= '-';
                return parseIntegerValue(type);

            case 'e': // real literal
                buffer.popFront();
                return parseReal();

            case 'c':
                buffer.popFront();
                if (!parseReal()) return fail();
                data ~= '+';
                if(!buffer.match('c')) return fail();
                if (!parseReal()) return fail();
                data ~= 'i';
                return success();

            case 'a': case 'w': case 'd':
                immutable char t = buffer.front;
                buffer.popFront();
                auto ret = decodeNumber();
                if(!ret) return fail();
                if(!buffer.match('_')) return fail();
                data ~= '"';
                foreach(i; 0..ret.get())
                {
                    auto a = ascii2hex(buffer.front);
                    if(!a) return fail();
                    buffer.popFront();
                    auto b = ascii2hex(buffer.front);
                    if(!b) return fail();
                    buffer.popFront();
                    auto v = cast(char)((a.get() << 4) | b.get());
                    if (' ' <= v && v <= '~')
                        data ~= v;
                    else
                    {
                        data ~= "\\x";
                        data.putAsHex(v, 2);
                    }
                }
                data ~= '"';
                if ('a' != t)
                    data ~= t;
                return success();

            case 'A': // array literal
                if ('H' == type)
                    goto case 'H';

                buffer.popFront();
                data ~= '[';
                auto ret = decodeNumber();
                if(!ret) return fail();
                foreach(i; 0..ret.get())
                {
                    if(i) data ~= ", ";
                    if(!parseValue()) return fail();
                }
                data ~= ']';
                return success();

            case 'H': // associative array literal
                buffer.popFront();
                data ~= '[';
                auto ret = decodeNumber();
                if(!ret) return fail();
                foreach(i; 0 .. ret.get())
                {
                    // handle commas
                    if (i) data ~= ", ";

                    // parse key
                    if (!parseValue()) return fail();
                    data ~= ':';
                    // parse value
                    if (!parseValue()) return fail();
                }
                data ~= ']';
                return success();

            case 'S':
                buffer.popFront();
                if (name.length)
                    data ~= name;
                data ~= '(';
                auto ret = decodeNumber();
                if(!ret) return fail();
                foreach (i; 0 .. ret.get())
                {
                    if (i) data ~= ", ";
                    if (!parseValue()) return fail();
                }
                data ~= ')';
                return success();

            case 'f':
                mixin(notImplementedParser);

            default: break;
        }

        return fail();
    }

    Result!void parseReal(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        switch (buffer.front)
        {
            case 'I':
                if(!buffer.match("INF")) return fail();
                data ~= "real.infinity";
                return success();
            case 'N':
                buffer.popFront();
                switch(buffer.front)
                {
                    case 'I':
                        if(!buffer.match("INF")) return fail();
                        data ~= "-real.infinity";
                        return success();
                    case 'A':
                        buffer.popFront();
                        if(!buffer.match('N')) return fail();
                        data ~= "real.nan";
                        return success();
                    default:
                        break;
                }
                data ~= '-';
                break;
            default:
                break;
        }

        switch (buffer.front)
        {
            // hex digits
            case '0': .. case '9':
            case 'a': .. case 'f':
            case 'A': .. case 'F':
                data ~= "0x";
                data ~= buffer.front();
                data ~= '.';
                buffer.popFront();

                while (isHexDigit(buffer.front))
                {
                    data ~= buffer.front();
                    buffer.popFront();
                }

                if(!buffer.match('P')) return fail();
                data ~= 'p';

                if (buffer.front == 'N')
                {
                    data ~= '-';
                    buffer.popFront();
                }

                while (isDigit(buffer.front))
                {
                    data ~= buffer.front();
                    buffer.popFront();
                }

                return success();

            default:
                return fail();
        }
    }

    //TODO: Add documentation
    Result!void parseIntegerValue(ParserFlags pf = ParserFlags.None)(char type)
    {
        mixin(initParser!());

        switch(type)
        {
            case 'a': case 'u': case 'w':
                auto retNumber = decodeNumber();
                if(!retNumber) return fail();
                immutable num = retNumber.get();
                switch(num)
                {
                    case '\'':
                        data ~= "'\\''";
                        break;
                    // \", \?
                    case '\\':
                        data ~= "'\\\\'";
                        break;
                    case '\a':
                        data ~= "'\\a'";
                        break;
                    case '\b':
                        data ~= "'\\b'";
                        break;
                    case '\f':
                        data ~= "'\\f'";
                        break;
                    case '\n':
                        data ~= "'\\n'";
                        break;
                    case '\r':
                        data ~= "'\\r'";
                        break;
                    case '\t':
                        data ~= "'\\t'";
                        break;
                    case '\v':
                        data ~= "'\\v'";
                        break;
                    default:
                        switch (type)
                        {
                            case 'a':
                                if (num >= 0x20 && num < 0x7F)
                                {
                                    data ~= '\'';
                                    data ~= cast(char)num;
                                    data ~= '\'';
                                    break;
                                }
                                data ~= "\\x";
                                data.putAsHex( num, 2 );
                                break;
                            case 'u':
                                data ~= "'\\u";
                                data.putAsHex( num, 4 );
                                data ~= '\'';
                                break;
                            case 'w':
                                data ~= "'\\U";
                                data.putAsHex( num, 8 );
                                data ~= '\'';
                                break;
                            default: return fail();
                        }
                }
                return success();

            case 'b':
                auto ret = decodeNumber();
                if(!ret) return fail();
                data ~= ret.get() ? "true" : "false";
                return success();

            case 'h', 't', 'k':
                auto ret = sliceNumberResult();
                if(!ret) return fail();
                data ~= ret.get();
                data ~= 'u';
                return success();

            case 'l':
                auto ret = sliceNumberResult();
                if(!ret) return fail();
                data ~= ret.get();
                data ~= 'L';
                return success();

            case 'm':
                auto ret = sliceNumberResult();
                if(!ret) return fail();
                data ~= ret.get();
                data ~= "uL";
                return success();

            default:
                auto ret = sliceNumberResult();
                if(!ret) return fail();
                data ~= ret.get();
                return success();
        }
    }

    /*
    Type:
        TypeModifiers(opt) TypeX
        TypeBackRef

    TypeModifiers:
        Const
        Wild
        Wild Const
        Shared
        Shared Const
        Shared Wild
        Shared Wild Const
        Immutable
    */
    /** Parse Type grammar node
     *
     * Params:
     *   tbuf = target buffer
     * Returns: true if successfully parsed, false otherwise
     */
    Result!(const(char)[]) parseType(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        static if (pf & ParserFlags.Silent)
        {
            auto rePos = data.arr.length;
            scope(exit) data.arr = data.arr[0 .. rePos];
        }

        // parse type back reference
        if(buffer.front == 'Q') return typeof(return)(parseTypeBackRef());

        static immutable string[23] primitiveTypes = [
            "char", // a
            "bool", // b
            "creal", // c
            "double", // d
            "real", // e
            "float", // f
            "byte", // g
            "ubyte", // h
            "int", // i
            "ireal", // j
            "uint", // k
            "long", // l
            "ulong", // m
            null, // n
            "ifloat", // o
            "idouble", // p
            "cfloat", // q
            "cdouble", // r
            "short", // s
            "ushort", // t
            "wchar", // u
            "void", // v
            "dchar", // w
        ];

        size_t beg = data.arr.length;

        // trust void initializers on this indirection as failed parsing should
        // never read that value
        alias Tret = typeof(return);
        typeof(return) ret = (() @trusted => Tret())();

        char t;
        // parse TypeModifiers and TypeX
        switch(t = buffer.front)
        {
            case 'y': // Immutable
                buffer.popFront();
                data ~= "immutable(";
                ret = parseType();
                if(!ret.success) return ret;
                data ~= ')';
                break;

            case 'O': // Shared
                buffer.popFront();
                data ~= "shared(";
                ret = parseType();
                if(!ret.success) return ret;
                data ~= ')';
                break;

            case 'x': // Const
                buffer.popFront();
                data ~= "const(";
                ret = parseType();
                if(!ret.success) return ret;
                data ~= ')';
                break;

            case 'N': // Wild
                buffer.popFront();
                switch (buffer.front)
                {
                    case 'g': // Wild (Ng Type)
                        buffer.popFront();
                        data ~= "inout(";
                        ret = parseType();
                        if(!ret.success) return ret;
                        data ~= ')';
                        break;

                    case 'h': // TypeVector (Nh Type)
                        buffer.popFront();
                        data ~= "vector(";
                        ret = parseType();
                        if(!ret.success) return ret;
                        data ~= ')';
                        break;

                    case 'n': // typeof(*null)
                        buffer.popFront();
                        data ~= "typeof(*null)";
                        break;
                    default:
                        return typeof(return)(fail());
                }
                if (buffer.peek(1) != 'g')
                    return typeof(return)(fail());
                buffer.popFront();
                buffer.popFront();
                data ~= "inout ";
                //TODO:
                if (buffer.front == 'x')
                    goto case 'x';
                break;

            case 'A': // Arrays
                buffer.popFront();
                ret = parseType();
                if(!ret.success) return ret;
                data ~= "[]";
                break;

            case 'G': // Static Arrays
                buffer.popFront();
                auto slice = sliceNumber();
                ret = parseType();
                if(!ret) return ret;
                data ~= '[';
                data ~= slice;
                data ~= ']';
                break;

            case 'H': // Associative Arrays
                buffer.popFront();
                ret = parseType();
                if(!ret.success) return ret;
                auto tx = ret.get();
                ret = parseType();
                if(!ret.success) return ret;
                data ~= '[';
                data ~= tx;
                data ~= ']';
                break;

            case 'C': // Classes
            case 'S': // Structs
            case 'E': // Enums
            case 'T': // Typedef
                buffer.popFront();
                parseQualifiedName();
                break;

            case 'D': // Delegates
                buffer.popFront();
                auto begPos = data.arr.length;
                parseTypeModifiers!(ParserFlags.Optional);
                auto endPos = data.arr.length;

                ret = parseTypeFunction!(ParserFlags.TFunctionDelegate);

                if(endPos - begPos)
                {
                    data.shiftEnd(endPos-1 , endPos);
                    data.shiftEnd(begPos, endPos-1);
                }
                break;

            case 'Z': // Internal symbol
                buffer.popFront();
                break;

            case 'a': .. case 'w': // Primitive Types
                buffer.popFront();
                data ~= primitiveTypes[cast(size_t)(t - 'a')];
                break;

            default: return typeof(return)(fail());
        }

        return typeof(return)(data.arr[beg .. data.arr.length]);
    }

    /*
    TypeFunction:
        TypeFunctionNoReturn Type
    */
    Result!(const(char)[]) parseTypeFunction(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        auto begPos = data.arr.length;
        data ~= ' ';

        static if (pf & ParserFlags.TFunctionDelegate)
            data ~= "delegate";
        else
            data ~= "function";

        if(!parseTypeFunctionNoReturn()) return typeof(return)(fail());

        auto endPos = data.arr.length;
        auto ret = parseType();
        data.shiftEnd(begPos, endPos);
        if(!ret.success) return ret;

        return ret;
    }

    Result!void parseTypeBackRef(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());
        mixin(notImplementedParser);
    }

    /*
    TemplateID:
        __T
        __U
    */
    bool isTemplateIDFront(ParserFlags pf = ParserFlags.None)()
    {
        mixin(initParser!());

        if(buffer.empty) return false;
        static if (!(pf & ParserFlags.EarlyIsParse))
        {
            auto bpos = buffer.pos;
            scope(exit) buffer.pos = bpos;
        }

        if(!buffer.match("__")) return false;
        switch(buffer.front)
        {
            case 'T':
            case 'U':
                return true;
            default: break;
        }

        return false;
    }

    bool isTypeFunctionNoReturnFront()
    {
        switch(buffer.front)
        {
            case 'F': // D
            case 'U': // C
            case 'W': // Windows
            case 'R': // C++
            case 'Y': // Objective-C
                return true;

            // error
            default: return false;
        }
    }

    // TODO: Support early parse
    bool isSymbolFunctionNameFront()
    {
        {
            char val = buffer.front;
            if (isDigit(val) || val == '_')
                return true;
            if (val != 'Q')
                return false;
        }

        // check the back reference encoding after 'Q'
        auto ret = peekBackref();
        if(ret.error) return false;
        return isDigit(ret.value); // identifier ref
    }

    static bool isDigit(char c)
    {
        return c - '0' < 10;
    }

    static bool isAlpha(char c)
    {
        return (c | 32) - 'a' < 26;
    }

    static bool isHexDigit(char c)
    {
        return ('0' <= c && '9' >= c) ||
               ('a' <= c && 'f' >= c) ||
               ('A' <= c && 'F' >= c);
    }

    static Result!ubyte ascii2hex(char val)
    {
        if (val >= 'a' && val <= 'f')
            return success(cast(ubyte)(val - 'a' + 10));
        if (val >= 'A' && val <= 'F')
            return success(cast(ubyte)(val - 'A' + 10));
        if (val >= '0' && val <= '9')
            return success(cast(ubyte)(val - '0'));

        return typeof(return)(fail());
    }


    //////////////////////////////////////////////////////////////////////////
    // Parsing Utility
    //////////////////////////////////////////////////////////////////////////

    /*
    Number:
        Digit
        Digit Number
    */
    const(char)[] sliceNumber() return scope
    {
        auto beg = buffer.pos;

        //TODO: improve this junky while (true)
        while (true)
        {
            if (!buffer.empty && isDigit(buffer.front))
                buffer.popFront();
            else
            {
                return buffer.buf[beg .. buffer.pos];
            }
        }
    }

    Result!(const(char)[]) sliceNumberResult() return scope
    {
        auto ret = sliceNumber();
        return result(ret, cast(bool)ret.length);
    }

    Result!size_t decodeNumber() scope
    {
        auto ret = sliceNumber();
        if(!ret.length) return typeof(return)(fail());
        return decodeNumber(ret);
    }

    Result!size_t decodeNumber(scope const(char)[] num) scope
    {
        size_t val;
        foreach (c; num)
        {
            import core.checkedint : mulu, addu;

            bool overflow;
            val = mulu(val, 10, overflow);
            val = addu(val, c - '0',  overflow);
            if (overflow)
                return fail!(typeof(return));
        }
        return success(val);
    }

    struct BackRefTuple(T)
    {
        int error;
        T value = void;
    }

    // return the first character at the back reference
    BackRefTuple!char peekBackref()
        in(buffer.front == 'Q')
    {
        auto ret = decodeBackref!1();
        if(ret.error) return BackRefTuple!char(ret.error);
        immutable n = ret.value;

        if (!n || n > buffer.pos)
            return BackRefTuple!char(Error.INVALID_BACKREF);

        char val = buffer.buf[buffer.pos - n];
        return BackRefTuple!char(0, val);
    }

    /*
    TypeBackRef:
        Q NumberBackRef

    IdentifierBackRef:
        Q NumberBackRef

    NumberBackRef:
        lower-case-letter
        upper-case-letter NumberBackRef
    */
    BackRefTuple!size_t decodeBackref(size_t peekAt = 0)()
    {
        size_t bref;
        enum base = 26;
        size_t n = 0;
        for (size_t p; ; p++)
        {
            char t;
            static if (peekAt > 0)
            {
                t = buffer.peek(peekAt + p);
            }
            else
            {
                t = buffer.front;
                buffer.popFront();
            }
            if (t < 'A' || t > 'Z')
            {
                if (t < 'a' || t > 'z')
                    return BackRefTuple!size_t(Error.INVALID_BACKREF);
                n = base * n + t - 'a';
                bref = n;
                break;
            }
            n = base * n + t - 'A';
        }

        return BackRefTuple!size_t(0, bref);
    }

    static bool contains( const(char)[] a, const(char)[] b ) @trusted
    {
        if (a.length && b.length)
        {
            auto bend = b.ptr + b.length;
            auto aend = a.ptr + a.length;
            return a.ptr <= b.ptr && bend <= aend;
        }
        return false;
    }

    enum Error : int {
        INVALID_BACKREF = 1,
    }

    struct BufferRange
    {
    nothrow pure @safe:
        this(return const(char)[] buf)
        {
            this.buf = buf;
        }

        char front() const scope
        {
            return buf[pos];
        }

        void popFront() scope
        {
            ++pos;
        }

        bool empty() const scope
        {
            return buf[pos..$].length == 0;
        }

        char peek(size_t n)
        {
            if ( pos + n < buf.length )
                return buf[pos + n];
            return char.init;
        }

        bool match(char val)
        {
            if(empty)
                return false;

            if (val == front)
            {
                popFront();
                return true;
            }

            return false;
        }

        bool match(const(char)[] val)
        {
            foreach(v; val)
                if(!match(v)) return false;

            return true;
        }

        const(char)[] buf; /// original buffer
        size_t pos; /// buffer position
    }

    struct Data
    {
    nothrow pure @safe:

        this(return char[] dst)
        {
            this.arr = dst[0 .. 0];
            this.capacity = dst.capacity;
        }

        void put(char val)
        {
            //FIXME: Improve and use provided dst buffer
            arr ~= val;
        }

        void put(scope const(char)[] val)
        {
            //FIXME: Improve and use provided dst buffer
            arr ~= val;
        }

        void putAsHex(size_t val, size_t width = 0)
        {
            import core.internal.string;

            UnsignedStringBuf buf = void;

            auto s = unsignedToTempString!16(val, buf);
            size_t slen = s.length;
            if (slen < width)
            {
                foreach (i; slen .. width)
                    put('0');
            }
            put(s);
        }

        alias opOpAssign(string op : "~") = put;

        void prepend(ParserFlags pf = ParserFlags.None)(const(char)[] buf)
        {
            if(pf & ParserFlags.OverrideData)
            {
                buf = buf.dup;

                foreach_reverse(i, c; arr[0 .. $ - buf.length])
                    arr[i + buf.length] = c;
                foreach(i, ref c; arr[0 .. buf.length]) c = buf[i];
            } else {
                //FIXME: Improve and use provided dst buffer
                arr = buf ~ arr;
            }
        }

        //TODO: Check if shift with allocation is better
        void shiftEnd(size_t beg, size_t end)
        {
            size_t remaining = arr.length - end;
            auto slice = arr[beg..$];

            while(remaining > 0)
            {
                auto temp=slice[$-1];
                for(size_t i = slice.length; i > 1; i--)
                    slice[i - 1] = slice[i - 2];
                slice[0] = temp;

                remaining--;
                /* debug(trace) printf("shiftEnd+loop: remaining=%d data='%.*s'\n", remaining, arr.length - beg, arr[beg..$].ptr); */
            }
        }

        void prepend(ParserFlags pf = ParserFlags.None)(char c)
        {
            prepend!(pf)([c]);
        }

        char[] arr;
        private size_t capacity;
    }

    BufferRange buffer;
    Data data;
}


/**
 * Demangles D mangled names.  If it is not a D mangled name, it returns its
 * argument name.
 *
 * Params:
 *  buf = The string to demangle.
 *  dst = An optional destination buffer.
 *
 * Returns:
 *  The demangled name or the original string if the name is not a mangled D
 *  name.
 */
char[] demangle( const(char)[] buf, char[] dst = null ) nothrow pure @safe
{
    return Demangler(buf, dst).doDemangle();
}

/**
 * Demangles a D mangled type.
 *
 * Params:
 *  buf = The string to demangle.
 *  dst = An optional destination buffer.
 *
 * Returns:
 *  The demangled type name or the original string if the name is not a
 *  mangled D type.
*/
char[] demangleType( const(char)[] buf, char[] dst = null ) nothrow pure @safe
{
    //TODO:
    return [];
}

/**
* reencode a mangled symbol name that might include duplicate occurrences
* of the same identifier by replacing all but the first occurence with
* a back reference.
*
* Params:
*  mangled = The mangled string representing the type
*
* Returns:
*  The mangled name with deduplicated identifiers
*/
char[] reencodeMangled(const(char)[] mangled) nothrow pure @safe
{
    //TODO:
    return [];
}

/**
 * Mangles a D symbol.
 *
 * Params:
 *  T = The type of the symbol.
 *  fqn = The fully qualified name of the symbol.
 *  dst = An optional destination buffer.
 *
 * Returns:
 *  The mangled name for a symbols of type T and the given fully
 *  qualified name.
 */
char[] mangle(T)(const(char)[] fqn, char[] dst = null) @safe pure nothrow
{
    import core.internal.string : numDigits, unsignedToTempString;

    static struct DotSplitter
    {
    @safe pure nothrow:
        const(char)[] s;

        @property bool empty() const { return !s.length; }

        @property const(char)[] front() const return
        {
            immutable i = indexOfDot();
            return i == -1 ? s[0 .. $] : s[0 .. i];
        }

        void popFront()
        {
            immutable i = indexOfDot();
            s = i == -1 ? s[$ .. $] : s[i+1 .. $];
        }

        private ptrdiff_t indexOfDot() const
        {
            foreach (i, c; s) if (c == '.') return i;
            return -1;
        }
    }

    size_t len = "_D".length;
    foreach (comp; DotSplitter(fqn))
        len += numDigits(comp.length) + comp.length;
    len += T.mangleof.length;
    if (dst.length < len) dst.length = len;

    size_t i = "_D".length;
    dst[0 .. i] = "_D";
    foreach (comp; DotSplitter(fqn))
    {
        const ndigits = numDigits(comp.length);
        unsignedToTempString(comp.length, dst[i .. i + ndigits]);
        i += ndigits;
        dst[i .. i + comp.length] = comp[];
        i += comp.length;
    }
    dst[i .. i + T.mangleof.length] = T.mangleof[];
    i += T.mangleof.length;

    static if (hasTypeBackRef)
        return reencodeMangled(dst[0 .. i]);
    else
        return dst[0 .. i];
}

//FIXME:
///
// @safe pure nothrow unittest
// {
//     assert(mangle!int("a.b") == "_D1a1bi");
//     assert(mangle!(char[])("test.foo") == "_D4test3fooAa");
//     assert(mangle!(int function(int))("a.b") == "_D1a1bPFiZi");
// }

//FIXME:
// @safe pure nothrow unittest
// {
//     static assert(mangle!int("a.b") == "_D1a1bi");

//     auto buf = new char[](10);
//     buf = mangle!int("a.b", buf);
//     assert(buf == "_D1a1bi");
//     buf = mangle!(char[])("test.foo", buf);
//     assert(buf == "_D4test3fooAa");
//     buf = mangle!(real delegate(int))("modµ.dg");
//     assert(buf == "_D5modµ2dgDFiZe", buf);
// }


/**
 * Mangles a D function.
 *
 * Params:
 *  T = function pointer type.
 *  fqn = The fully qualified name of the symbol.
 *  dst = An optional destination buffer.
 *
 * Returns:
 *  The mangled name for a function with function pointer type T and
 *  the given fully qualified name.
 */
char[] mangleFunc(T:FT*, FT)(const(char)[] fqn, char[] dst = null) @safe pure nothrow if (is(FT == function))
{
    static if (isExternD!FT)
    {
        return mangle!FT(fqn, dst);
    }
    else static if (hasPlainMangling!FT)
    {
        dst.length = fqn.length;
        dst[] = fqn[];
        return dst;
    }
    else static if (isExternCPP!FT)
    {
        static assert(0, "Can't mangle extern(C++) functions.");
    }
    else
    {
        static assert(0, "Can't mangle function with unknown linkage ("~FT.stringof~").");
    }
}

private enum hasTypeBackRef = (int function(void**,void**)).mangleof[$-4 .. $] == "QdZi";

// @safe pure nothrow unittest
// {
//     assert(mangleFunc!(int function(int))("a.b") == "_D1a1bFiZi");
//     static if (hasTypeBackRef)
//     {
//         assert(mangleFunc!(int function(Object))("object.Object.opEquals") == "_D6object6Object8opEqualsFCQsZi");
//         assert(mangleFunc!(int function(Object, Object))("object.Object.opEquals") == "_D6object6Object8opEqualsFCQsQdZi");
//     }
//     else
//     {
//         auto mngl = mangleFunc!(int function(Object))("object.Object.opEquals");
//         assert(mngl == "_D6object6Object8opEqualsFC6ObjectZi");
//         auto remngl = reencodeMangled(mngl);
//         assert(remngl == "_D6object6Object8opEqualsFCQsZi");
//     }
//     // trigger back tracking with ambiguity on '__T', template or identifier
//     assert(reencodeMangled("_D3std4conv4conv7__T3std4convi") == "_D3std4convQf7__T3stdQpi");
// }

// @safe pure nothrow unittest
// {
//     int function(lazy int[], ...) fp;
//     assert(mangle!(typeof(fp))("demangle.test") == "_D8demangle4testPFLAiYi");
//     assert(mangle!(typeof(*fp))("demangle.test") == "_D8demangle4testFLAiYi");
// }

private template isExternD(FT) if (is(FT == function))
{
    enum isExternD = __traits(getLinkage, FT) == "D";
}

private template isExternCPP(FT) if (is(FT == function))
{
    enum isExternCPP = __traits(getLinkage, FT) == "C++";
}

private template hasPlainMangling(FT) if (is(FT == function))
{
    enum lnk = __traits(getLinkage, FT);
    // C || Windows
    enum hasPlainMangling = lnk == "C" || lnk == "Windows";
}

@safe pure nothrow unittest
{
    static extern(D) void fooD();
    static extern(C) void fooC();
    static extern(Windows) void fooW();
    static extern(C++) void fooCPP();

    bool check(FT)(bool isD, bool isCPP, bool isPlain)
    {
        return isExternD!FT == isD && isExternCPP!FT == isCPP &&
            hasPlainMangling!FT == isPlain;
    }
    static assert(check!(typeof(fooD))(true, false, false));
    static assert(check!(typeof(fooC))(false, false, true));
    static assert(check!(typeof(fooW))(false, false, true));
    static assert(check!(typeof(fooCPP))(false, true, false));

    static assert(__traits(compiles, mangleFunc!(typeof(&fooD))("")));
    static assert(__traits(compiles, mangleFunc!(typeof(&fooC))("")));
    static assert(__traits(compiles, mangleFunc!(typeof(&fooW))("")));
    static assert(!__traits(compiles, mangleFunc!(typeof(&fooCPP))("")));
}

/***
 * C name mangling is done by adding a prefix on some platforms.
 */
version (Win32)
    enum string cPrefix = "_";
else version (Darwin)
    enum string cPrefix = "_";
else
    enum string cPrefix = "";

@safe pure nothrow unittest
{
    immutable string[2][] table =
        [
            ["_D4test2dgDFiYd", "double delegate(int, ...) test.dg"],
            ["_D4test2dgDxFNfiYd", "double delegate(int, ...) @safe const test.dg"],
            ["printf", "printf"],
            ["_foo", "_foo"],
            ["_D88", "_D88"],
            ["_D3fooQeFIAyaZv", "void foo.foo(in immutable(char)[])" ],
            ["_D3barQeFIKAyaZv", "void bar.bar(in ref immutable(char)[])" ],
            ["_D4test3fooAa", "char[] test.foo"],
            ["_D8demangle8demangleFAaZAa", "char[] demangle.demangle(char[])"],
            ["_D6object6Object8opEqualsFC6ObjectZi", "int object.Object.opEquals(Object)"],
            //["_D4test58__T9factorialVde67666666666666860140VG5aa5_68656c6c6fVPvnZ9factorialf", ""],
            //["_D4test101__T9factorialVde67666666666666860140Vrc9a999999999999d9014000000000000000c00040VG5aa5_68656c6c6fVPvnZ9factorialf", ""],
            ["_D8demangle4testFAiYi", "int demangle.test(int[], ...)"],
            ["_D8demangle4testFLAiXi", "int demangle.test(lazy int[]...)"],
            ["_D8demangle4testFLAiYi", "int demangle.test(lazy int[], ...)"],
            ["_D6plugin8generateFiiZAya", "immutable(char)[] plugin.generate(int, int)"],
            ["_D6plugin8generateFiiZAxa", "const(char)[] plugin.generate(int, int)"],
            ["_D6plugin8generateFiiZAOa", "shared(char)[] plugin.generate(int, int)"],
            ["_D8demangle4testFAiXi", "int demangle.test(int[]...)"],
            ["_D8demangle4testFLC6ObjectLDFLiZiZi", "int demangle.test(lazy Object, lazy int delegate(lazy int))"],
            ["_D8demangle3fnAFZ3fnBMFZv", "void demangle.fnA().fnB()"],
            ["_D8demangle4mainFZ1S3fnCMFZv", "void demangle.main().S.fnC()"],
            ["_D8demangle4mainFZ1S3fnDMFZv", "void demangle.main().S.fnD()"],
            ["_D4test34__T3barVG3uw3_616263VG3wd3_646566Z1xi", "int test.bar!(\"abc\"w, \"def\"d).x"],
            ["_D8demangle20__T2fnVAiA4i1i2i3i4Z2fnFZv", "void demangle.fn!([1, 2, 3, 4]).fn()"],
            ["_D8demangle10__T2fnVi1Z2fnFZv", "void demangle.fn!(1).fn()"],
            ["_D8demangle26__T2fnVS8demangle1SS2i1i2Z2fnFZv", "void demangle.fn!(demangle.S(1, 2)).fn()"],
            ["_D8demangle21__T2fnVHiiA2i1i2i3i4Z2fnFZv", "void demangle.fn!([1:2, 3:4]).fn()"],
            ["_D8demangle13__T2fnVeeNANZ2fnFZv", "void demangle.fn!(real.nan).fn()"],
            ["_D8demangle14__T2fnVeeNINFZ2fnFZv", "void demangle.fn!(-real.infinity).fn()"],
            ["_D8demangle13__T2fnVeeINFZ2fnFZv", "void demangle.fn!(real.infinity).fn()"],
            ["_D8demangle2fnFNgiZNgi", "inout(int) demangle.fn(inout(int))"],
            ["_D8demangle29__T2fnVa97Va9Va0Vu257Vw65537Z2fnFZv", "void demangle.fn!('a', '\\t', \\x00, '\\u0101', '\\U00010001').fn()"],
            ["_D2gc11gctemplates56__T8mkBitmapTS3std5range13__T4iotaTiTiZ4iotaFiiZ6ResultZ8mkBitmapFNbNiNfPmmZv",
             "nothrow @nogc @safe void gc.gctemplates.mkBitmap!(std.range.iota!(int, int).iota(int, int).Result).mkBitmap(ulong*, ulong)"],
            ["_D8serenity9persister6Sqlite69__T15SqlitePersisterTS8serenity9persister6Sqlite11__unittest6FZ4TestZ15SqlitePersister12__T7opIndexZ7opIndexMFmZS8serenity9persister6Sqlite11__unittest6FZ4Test",
             "serenity.persister.Sqlite.__unittest6().Test serenity.persister.Sqlite.SqlitePersister!(serenity.persister.Sqlite.__unittest6().Test).SqlitePersister.opIndex!().opIndex(ulong)"],
            ["_D8bug100274mainFZ5localMFZi","int bug10027.main().local()"],
            ["_D8demangle4testFNhG16gZv", "void demangle.test(__vector(byte[16]))"],
            ["_D8demangle4testFNhG8sZv", "void demangle.test(__vector(short[8]))"],
            ["_D8demangle4testFNhG4iZv", "void demangle.test(__vector(int[4]))"],
            ["_D8demangle4testFNhG2lZv", "void demangle.test(__vector(long[2]))"],
            ["_D8demangle4testFNhG4fZv", "void demangle.test(__vector(float[4]))"],
            ["_D8demangle4testFNhG2dZv", "void demangle.test(__vector(double[2]))"],
            ["_D8demangle4testFNhG4fNhG4fZv", "void demangle.test(__vector(float[4]), __vector(float[4]))"],
            ["_D8bug1119234__T3fooS23_D8bug111924mainFZ3bariZ3fooMFZv","void bug11192.foo!(bug11192.main().bar).foo()"],
            ["_D13libd_demangle12__ModuleInfoZ", "libd_demangle.__ModuleInfo"],
            ["_D15TypeInfo_Struct6__vtblZ", "TypeInfo_Struct.__vtbl"],
            ["_D3std5stdio12__ModuleInfoZ", "std.stdio.__ModuleInfo"],
            ["_D3std6traits15__T8DemangleTkZ8Demangle6__initZ", "std.traits.Demangle!(uint).Demangle.__init"],
            ["_D3foo3Bar7__ClassZ", "foo.Bar.__Class"],
            ["_D3foo3Bar6__vtblZ", "foo.Bar.__vtbl"],
            ["_D3foo3Bar11__interfaceZ", "foo.Bar.__interface"],
            ["_D3foo7__arrayZ", "foo.__array"],
            ["_D8link657428__T3fooVE8link65746Methodi0Z3fooFZi", "int link6574.foo!(0).foo()"],
            ["_D8link657429__T3fooHVE8link65746Methodi0Z3fooFZi", "int link6574.foo!(0).foo()"],
            ["_D4test22__T4funcVAyaa3_610a62Z4funcFNaNbNiNmNfZAya", `pure nothrow @nogc @live @safe immutable(char)[] test.func!("a\x0ab").func()`],
            ["_D3foo3barFzkZzi", "cent foo.bar(ucent)"],
            ["_D5bug145Class3fooMFNlZPv", "scope void* bug14.Class.foo()"],
            ["_D5bug145Class3barMFNjZPv", "return void* bug14.Class.bar()"],
            ["_D5bug143fooFMPvZPv", "void* bug14.foo(scope void*)"],
            ["_D5bug143barFMNkPvZPv", "void* bug14.bar(scope return void*)"],
            ["_D3std5range15__T4iotaTtTtTtZ4iotaFtttZ6Result7opIndexMNgFNaNbNiNfmZNgt",
             "inout pure nothrow @nogc @safe inout(ushort) std.range.iota!(ushort, ushort, ushort).iota(ushort, ushort, ushort).Result.opIndex(ulong)"],
            ["_D3std6format77__T6getNthVAyaa13_696e7465676572207769647468S233std6traits10isIntegralTiTkTkZ6getNthFNaNfkkkZi",
             "pure @safe int std.format.getNth!(\"integer width\", std.traits.isIntegral, int, uint, uint).getNth(uint, uint, uint)"],
            ["_D3std11parallelism42__T16RoundRobinBufferTDFKAaZvTDxFNaNdNeZbZ16RoundRobinBuffer5primeMFZv",
             "void std.parallelism.RoundRobinBuffer!(void delegate(ref char[]), bool delegate() pure @property @trusted const).RoundRobinBuffer.prime()"],
            // Lname '0'
            ["_D3std9algorithm9iteration__T9MapResultSQBmQBlQBe005stripTAAyaZQBi7opSliceMFNaNbNiNfmmZSQDiQDhQDa__TQCtSQDyQDxQDq00QCmTQCjZQDq",
             "pure nothrow @nogc @safe std.algorithm.iteration.MapResult!(std.algorithm.iteration.__anonymous.strip, "
            ~"immutable(char)[][]).MapResult std.algorithm.iteration.MapResult!(std.algorithm.iteration.strip, immutable(char)[][]).MapResult.opSlice(ulong, ulong)"],

            // back references
            ["_D4core4stdc5errnoQgFZi", "int core.stdc.errno.errno()"], // identifier back reference
            ["_D4testFS10structnameQnZb", "bool test(structname, structname)"], // type back reference
            ["_D3std11parallelism__T4TaskS8unittest3cmpTAyaTQeZQBb6__dtorMFNfZv",
            "@safe void std.parallelism.Task!(unittest.cmp, immutable(char)[], immutable(char)[]).Task.__dtor()"],
            // 1.s.s.foo from https://issues.dlang.org/show_bug.cgi?id=15831
            ["_D13testexpansion44__T1sTS13testexpansion8__T1sTiZ1sFiZ6ResultZ1sFS13testexpansion8__T1sTiZ1sFiZ6ResultZ6Result3fooMFNaNfZv",
             "pure @safe void testexpansion.s!(testexpansion.s!(int).s(int).Result).s(testexpansion.s!(int).s(int).Result).Result.foo()"],
            ["_D13testexpansion__T1sTSQw__TQjTiZQoFiZ6ResultZQBbFQBcZQq3fooMFNaNfZv",
             "pure @safe void testexpansion.s!(testexpansion.s!(int).s(int).Result).s(testexpansion.s!(int).s(int).Result).Result.foo()"],
            // formerly ambiguous on 'V', template value argument or pascal function
            // pascal functions have now been removed (in v2.095.0)
            ["_D3std4conv__T7enumRepTyAaTEQBa12experimental9allocator15building_blocks15stats_collector7OptionsVQCti64ZQDnyQDh",
             "immutable(char[]) std.conv.enumRep!(immutable(char[]), std.experimental.allocator.building_blocks.stats_collector.Options, 64).enumRep"],
            // symbol back reference to location with symbol back reference
            ["_D3std12experimental9allocator6common__T10reallocateTSQCaQBzQBo15building_blocks17kernighan_ritchie__T8KRRegionTSQEhQEgQDvQCh14null_allocator13NullAllocatorZQCdZQErFNaNbNiKQEpKAvmZb",
             "pure nothrow @nogc bool std.experimental.allocator.common.reallocate!(std.experimental.allocator.building_blocks.kernighan_ritchie.KRRegion!("
            ~"std.experimental.allocator.building_blocks.null_allocator.NullAllocator).KRRegion).reallocate(ref "
            ~"std.experimental.allocator.building_blocks.kernighan_ritchie.KRRegion!(std.experimental.allocator.building_blocks.null_allocator.NullAllocator).KRRegion, ref void[], ulong)"],
            ["_D3std9exception__T11doesPointToTASQBh5regex8internal2ir10NamedGroupTQBkTvZQCeFNaNbNiNeKxASQDlQCeQCbQBvQBvKxQtZb",
             "pure nothrow @nogc @trusted bool std.exception.doesPointTo!(std.regex.internal.ir.NamedGroup[], "
            ~"std.regex.internal.ir.NamedGroup[], void).doesPointTo(ref const(std.regex.internal.ir.NamedGroup[]), ref const(std.regex.internal.ir.NamedGroup[]))"],
            ["_D3std9algorithm9iteration__T14SplitterResultS_DQBu3uni7isWhiteFNaNbNiNfwZbTAyaZQBz9__xtoHashFNbNeKxSQDvQDuQDn__TQDgS_DQEnQCtQCsQCnTQCeZQEdZm",
             "nothrow @trusted ulong std.algorithm.iteration.SplitterResult!(std.uni.isWhite(dchar), immutable(char)[]).SplitterResult."
            ~"__xtoHash(ref const(std.algorithm.iteration.SplitterResult!(std.uni.isWhite, immutable(char)[]).SplitterResult))"],
            ["_D3std8typecons__T7TypedefTCQBaQz19__unittestL6513_208FNfZ7MyClassVQBonVAyanZQCh6__ctorMFNaNbNcNiNfQCuZSQDyQDx__TQDrTQDmVQDqnVQCcnZQEj",
             "pure nothrow ref @nogc @safe std.typecons.Typedef!(std.typecons.__unittestL6513_208().MyClass, null, null).Typedef "
            ~"std.typecons.Typedef!(std.typecons.__unittestL6513_208().MyClass, null, null).Typedef.__ctor(std.typecons.__unittestL6513_208().MyClass)"],
            ["_D3std6getopt__TQkTAyaTDFNaNbNiNfQoZvTQtTDQsZQBnFNfKAQBiQBlQBkQBrQyZSQCpQCo12GetoptResult",
             "@safe std.getopt.GetoptResult std.getopt.getopt!(immutable(char)[], void delegate(immutable(char)[]) pure nothrow @nogc @safe, "
            ~"immutable(char)[], void delegate(immutable(char)[]) pure nothrow @nogc @safe)."
            ~"getopt(ref immutable(char)[][], immutable(char)[], void delegate(immutable(char)[]) pure nothrow @nogc @safe, "
            ~"immutable(char)[], void delegate(immutable(char)[]) pure nothrow @nogc @safe)"],
            ["_D3std5regex8internal9kickstart__T7ShiftOrTaZQl11ShiftThread__T3setS_DQCqQCpQCmQCg__TQBzTaZQCfQBv10setInvMaskMFNaNbNiNfkkZvZQCjMFNaNfwZv",
             "pure @safe void std.regex.internal.kickstart.ShiftOr!(char).ShiftOr.ShiftThread.set!(std.regex.internal.kickstart.ShiftOr!(char).ShiftOr.ShiftThread.setInvMask(uint, uint)).set(dchar)"],
            ["_D3std5stdio4File__T8lockImplX10LockFileExTykZQBaMFmmykZi", // C function as template alias parameter
             "int std.stdio.File.lockImpl!(LockFileEx, immutable(uint)).lockImpl(ulong, ulong, immutable(uint))"],
            // back reference for type in template AA parameter value
            ["_D3std9algorithm9iteration__T12FilterResultSQBq8typecons__T5TupleTiVAyaa1_61TiVQla1_62TiVQva1_63ZQBm__T6renameVHiQBtA2i0a1_63i2a1_61ZQBeMFNcZ9__lambda1TAiZQEw9__xtoHashFNbNeKxSQGsQGrQGk__TQGdSQHiQFs__TQFmTiVQFja1_61TiVQFua1_62TiVQGfa1_63ZQGx__TQFlVQFhA2i0a1_63i2a1_61ZQGjMFNcZQFfTQEyZQJvZm",
             `nothrow @trusted ulong std.algorithm.iteration.FilterResult!(std.typecons.Tuple!(int, "a", int, "b", int, "c").`
            ~`Tuple.rename!([0:"c", 2:"a"]).rename().__lambda1, int[]).FilterResult.__xtoHash(ref const(std.algorithm.iteration.`
            ~`FilterResult!(std.typecons.Tuple!(int, "a", int, "b", int, "c").Tuple.rename!([0:"c", 2:"a"]).rename().__lambda1, int[]).FilterResult))`],
        ];

        foreach ( i, name; table )
        {
            import std.datetime.stopwatch : benchmark;
            import std.stdio;

            debug(benchmark) {
                auto b = benchmark!(
                    () => demangle(name[0]),
                    () {
                        import coreo.demangle;
                        coreo.demangle.demangle(name[0]);
                    })(100_000);

                writefln("BENCHMARK:\nNEW %s\nOLD %s", b[0], b[1]);
            }
            auto r = demangle( name[0] );
            debug(trace) stdout.flush();
            assert( r == name[1],
                    "demangled `" ~ name[0] ~ "` as `" ~ r ~ "` but expected `" ~ name[1] ~ "`");
        }

        //FIXME: Activate this after everything is working
        /*
        template staticIota(int x)
        {
            template Seq(T...){ alias Seq = T; }

            static if (x == 0)
                alias staticIota = Seq!();
            else
                alias staticIota = Seq!(staticIota!(x - 1), x - 1);
        }

        foreach ( i; staticIota!(table.length) )
        {
            enum r = demangle( table[i][0] );
            static assert( r == table[i][1],
                    "demangled `" ~ table[i][0] ~ "` as `" ~ r ~ "` but expected `" ~ table[i][1] ~ "`");
        }

        {
            // https://issues.dlang.org/show_bug.cgi?id=18531
            auto symbol = `_D3std3uni__T6toCaseS_DQvQt12toLowerIndexFNaNbNiNewZtVii1043S_DQCjQCi10toLowerTabFNaNbNiNemZwSQDo5ascii7toLowerTAyaZQDzFNaNeQmZ14__foreachbody2MFNaNeKmKwZ14__foreachbody3MFNaNeKwZi`;
            auto demangled = `pure @trusted int std.uni.toCase!(std.uni.toLowerIndex(dchar), 1043, std.uni.toLowerTab(ulong), std.ascii.toLower, immutable(char)[]).toCase(immutable(char)[]).__foreachbody2(ref ulong, ref dchar).__foreachbody3(ref dchar)`;
            auto dst = new char[200];
            auto ret = demangle( symbol, dst);
            assert( ret == demangled );
        }
        */
}

// unittest
// {
//     // https://issues.dlang.org/show_bug.cgi?id=18300
//     string s = demangle.mangleof;
//     foreach (i; 1..77)
//     {
//         char[] buf = new char[i];
//         auto ds = demangle(s, buf);
//         assert(ds == "pure nothrow @safe char[] core.demangle.demangle(const(char)[], char[])");
//     }
// }

// unittest
// {
//     // https://issues.dlang.org/show_bug.cgi?id=18300
//     string s = "_D1";
//     string expected = "int ";
//     foreach (_; 0..10_000)
//     {
//         s ~= "a1";
//         expected ~= "a.";
//     }
//     s ~= "FiZi";
//     expected ~= "F";
//     assert(s.demangle == expected);
// }

/*
 *
 */
string decodeDmdString( const(char)[] ln, ref size_t p ) nothrow pure @safe
{
    string s;
    uint zlen, zpos;

    // decompress symbol
    while ( p < ln.length )
    {
        int ch = cast(ubyte) ln[p++];
        if ( (ch & 0xc0) == 0xc0 )
        {
            zlen = (ch & 0x7) + 1;
            zpos = ((ch >> 3) & 7) + 1; // + zlen;
            if ( zpos > s.length )
                break;
            s ~= s[$ - zpos .. $ - zpos + zlen];
        }
        else if ( ch >= 0x80 )
        {
            if ( p >= ln.length )
                break;
            int ch2 = cast(ubyte) ln[p++];
            zlen = (ch2 & 0x7f) | ((ch & 0x38) << 4);
            if ( p >= ln.length )
                break;
            int ch3 = cast(ubyte) ln[p++];
            zpos = (ch3 & 0x7f) | ((ch & 7) << 7);
            if ( zpos > s.length )
                break;
            s ~= s[$ - zpos .. $ - zpos + zlen];
        }
        else if ( Demangler.isAlpha(cast(char)ch) || Demangler.isDigit(cast(char)ch) || ch == '_' )
            s ~= cast(char) ch;
        else
        {
            p--;
            break;
        }
    }
    return s;
}

// locally purified for internal use here only
extern (C) private
{
    pure @trusted @nogc nothrow pragma(mangle, "fakePureReprintReal") void pureReprintReal(char[] nptr);

    void fakePureReprintReal(char[] nptr)
    {
        import core.stdc.stdlib : strtold;
        import core.stdc.stdio : snprintf;
        import core.stdc.errno : errno;

        const err = errno;
        real val = strtold(nptr.ptr, null);
        snprintf(nptr.ptr, nptr.length, "%#Lg", val);
        errno = err;
    }
}

