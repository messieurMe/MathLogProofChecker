class FinalParser {
    private var pos: Int = 0
    private lateinit var s: String
    private fun posCheck() = pos < s.length
    private fun isVar() = (s[pos].isLetterOrDigit() /*|| s[pos] == '\''*/)
    private fun pp(inc: Int = 1, res: String = ""): String {
        pos += inc
        skip()
        return res
    }

    private fun readVarName(): String {
        return if (posCheck() && isVar()) s[pos++].plus(readVarName()) else ""
    }

    private fun skip() {
        while (posCheck() && s[pos] == ' ') pos++
    }

    private fun readNext(): String {
        if (!posCheck()) return ""
        return when (s[pos]) {
            '&' -> pp(0, "&")
            '!' -> pp(0, "!")
            '-' -> pp(0, "->")
            '(' -> pp(0, "(")
            ')' -> pp(0, ")")
            '=' -> pp(0, "=")
            '+' -> pp(0, "+")
            '*' -> pp(0, "*")
            '\'' -> pp(0, "'")
            '@' -> pp(0, "@")
            '?' -> pp(0, "?")
            '|' -> if (s[pos + 1] == '-') pp(0, "|-") else pp(0, "|")
            else -> readVarName()
        }
    }

    private fun parseVar(): FinalExpression {
        return when (val next = readNext()) {
            "(", ")" -> {
                pp()
                skip()
                val a = parseImpl()
                pp()
                skip()
                a
            }
            "!" -> {
                pp(1)
                skip()
                FinalExpression("!", use(parseEq()), null)
            }
            //@a.qyreuiq
            "@", "?" -> {
                pp(1)
                skip()
                FinalExpression(next, use(parseVar()).also { skip() }.also { pp(1) }, use(parseImpl()))
            }
            else -> {
                skip()
                FinalExpression(next, null, null)
            }
        }
    }

    private fun universalFunction(
        fromAnd: Boolean,
        const: String,
        recFun: () -> FinalExpression,
        whileFun: () -> FinalExpression? = ::parseImpl,
        isNotNull: Boolean = true
    ): FinalExpression {
        skip()
        var parsingResult: FinalExpression = recFun()
        skip()
        while (posCheck() && readNext() == const) {
            pp(if (fromAnd) 2 else 1, "")
            skip()
            parsingResult =
                FinalExpression(const, use(parsingResult), if (isNotNull) use(whileFun()!!) else null)
            skip()
        }
        skip()
        return parsingResult
    }

    private fun parseApostrophe() = universalFunction(false, "'", ::parseVar, { null },false)
    private fun parseMultiply() = universalFunction(false, "*", ::parseApostrophe, ::parseApostrophe)
    private fun parseSun() = universalFunction(false, "+", ::parseMultiply, ::parseMultiply)
    private fun parseEq() = universalFunction(false, "=", ::parseSun, ::parseSun)

    private fun parseAnd() = universalFunction(false, "&", ::parseEq, ::parseEq)
    private fun parseOr() = universalFunction(false, "|", ::parseAnd, ::parseAnd)
    private fun parseImpl() = universalFunction(true, "->", ::parseOr)

    fun parse(s: String): FinalExpression {
        pos = 0
        this.s = s
        return parseImpl().also { this.s = "" }
    }
}