data class FinalExpression(var op: String, var l: Int?, var r: Int?) {
    private fun weNeedHypo(e: FinalExpression?): Boolean {
        return (this.op == e?.op)
                && (get(l)?.weNeedHypo(get(e.l)) ?: (l == e.l))
                && (get(r)?.weNeedHypo(get(e.r)) ?: (r == e.r))
    }

    fun weNeedAxiom(e: Int?): Boolean {
        if (get(e)?.op != null && get(e)!!.l == null && get(e)!!.r == null) {
            return if (isWas[get(e)!!.op] != null) {
                weNeedHypo(isWas[get(e)!!.op])
            } else {
                true.also { isWas[get(e)!!.op] = this }
            }
        }
        return (this.op == get(e)?.op)
                && (get(l)?.weNeedAxiom(get(e)?.l) ?: (l == get(e)?.l))
                && (get(r)?.weNeedAxiom(get(e)?.r) ?: (r == get(e)?.r))
    }

    fun stringView(): String {
        return if (r != null && l != null) {
            if (op == "@" || op == "?") {
                ("(" + op + get(l)!!.stringView() + "." + get(r)!!.stringView() + ")")
            } else {
                ("(" + (get(l)?.stringView() ?: "") + op + (get(r)?.stringView() ?: "") + ")")
            }
        } else if (l != null) {
            if (op == "'") {
                ("${get(l)?.stringView()}'")
            } else {
                ("(" + op + (get(l)?.stringView() ?: "") + ")")
            }
        } else {
            op
        }
    }

    fun gL() = allData[l]
    fun gR() = allData[r]

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as FinalExpression

        if (op != other.op) return false
        if (l != other.l) return false
        if (r != other.r) return false

        return true
    }


    override fun hashCode(): Int {
        var result = op.hashCode()
        result = 3571 * result + (l?.hashCode() ?: 0)
        result = 27644437 * result + (r?.hashCode() ?: 0)
        result *= 1471
        val str = this.op + l.toString() + r.toString()
        var i = 1
        for (ch in str) {
            result += ch.hashCode() * i
            i *= 31
        }
        return result
    }
}
