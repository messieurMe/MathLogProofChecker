import java.util.*
import java.io.BufferedReader
import java.io.InputStreamReader
import kotlin.system.exitProcess
import kotlin.collections.HashMap
import kotlin.collections.HashSet
import kotlin.collections.ArrayList


fun main(args: Array<String>) {

    val parser: FinalParser? = FinalParser()
    println(parser!!.parse("!!A->A").stringView())
//    val sc = BufferedReader(InputStreamReader(System.`in`))
    val sc = Scanner(System.`in`)
    var firstEx = true
    var weMustExpr: Int? = null
    fillAx(parser)
    ((" ").plus(sc.nextLine())).split("|-")
        .also {
            (it[0].plus(""))
                .trim()
                .split(",")
                .forEach { j -> hypos.add(use(parser.parse(j))) }
        }
        .also { weMustExpr = use(parser.parse(it[1])) }
    if (hypos.isNotEmpty() && get(hypos[hypos.size - 1])!!.stringView() == "()") {
        hypos.removeAt(hypos.size - 1)
    }
    println("|-${weMustExpr!!.getExp()!!.stringView()}")
//    if(sc.hasNext())println("Ready")
    while ((sc.hasNext()) && !stop) {
        size += 1
        sentence = use(parser.parse(sc.nextLine()))

        if (checkMainAx() || checkFormalAx() || checkImpl() || penetrationRules()) {
            if (weDid.containsKey(sentence)) {
                weDid.replace(sentence, Data(0, size, AX))
            } else {
                weDid.put(sentence, Data(0, size, AX))
            }
//            weDid[sentence] = Data(0, size, AX)
            if (get(sentence)!!.op == "->") {
                if (!implications.containsKey(get(sentence)!!.r!!)) {
                    implications[get(sentence)!!.r!!] = HashSet()
                }
                implications[get(sentence)!!.r!!]!!.add(sentence)
            }
            continue
        }
        println("Expression $size is not proved.")
        exitProcess(0)
    }
    if (!weMustExpr!!.equals(sentence)) println("The proof proves different expression.")
    sc.close()
}

fun penetrationRules(): Boolean {
    if (sentence.getExp()?.op != "->") return false

    if (sentence.getExp()?.gL()?.op == "?") {
        val left = sentence.getExp()?.gL()?.gR()
        val right = sentence.getExp()?.gR()
        if (weDid.containsKey(use(FinalExpression("->", use(left!!), use(right!!))))) {
            allVariables.clear()
            allVariables.add(sentence.getExp()!!.gL()!!.gL()!!.op)
            if (!isSlave(right)) {
                println("Expression $size: variable ${sentence.getExp()!!.gL()!!.gL()!!.op} occurs free in ?@-rule.")
                stop = true//Correct message, exit code
                exitProcess(0)
            } else {
                println(
                    "[$size. ?@-intro ${
                    weDid[use(
                        FinalExpression(
                            "->",
                            use(left),
                            use(right)
                        )
                    )]!!.last
                    }] ${sentence.getExp()!!.stringView()}"
                )
                return true
            }
        }
    }
    if (sentence.getExp()!!.gR()?.op == "@") {
        val left = sentence.getExp()!!.gL()
        val right = sentence.getExp()!!.gR()!!.gR()
        if (weDid.containsKey(use(FinalExpression("->", use(left!!), use(right!!))))) {
            allVariables.clear()
            allVariables.add(sentence.getExp()!!.gR()!!.gL()!!.op)
            if (!isSlave(left)) {
                println("Expression $size: variable ${sentence.getExp()!!.gR()!!.gL()!!.op} occurs free in ?@-rule.")
                stop = true//same
                exitProcess(0)
            } else {
                println(
                    "[$size. ?@-intro ${
                    weDid[use(
                        FinalExpression(
                            "->",
                            use(left),
                            use(right)
                        )
                    )]!!.last
                    }] ${sentence.getExp()!!.stringView()}"
                )
                return true
            }
        }
    }
    return false
}

var stop = false
var counter = 0

const val MP = "M.P."
const val AX = "Ax. sch."

val HYPO = "Hypothesis"

var allData: HashMap<Int, FinalExpression> = HashMap()
var size = 0

var sentence: Int = 0
val hypos: ArrayList<Int> = ArrayList()

val axiomas: LinkedList<Int> = LinkedList()
val formalAxiomas: LinkedList<Int> = LinkedList()

var weDid: HashMap<Int, Data> = HashMap()
var implications: HashMap<Int, HashSet<Int>> = HashMap()


//fun use(finalExpression: FinalExpression) = finalExpression.hashCode().also { allData[it] = finalExpression }
fun use(finalExpression: FinalExpression): Int {
    if (allData.containsKey(finalExpression.hashCode())) {
        checkRec(finalExpression, allData[finalExpression.hashCode()])
    }
    return finalExpression.hashCode().also { allData[it] = finalExpression }
}

fun checkRec(feF: FinalExpression?, feS: FinalExpression?): Boolean {
    if (feF == null && feS == null) return true
//    if(!(feF?.equals(feS)))
    if (feF == null && feS != null) return false
    if (feF != null && feS == null) return false
    return if (feF?.op == feS?.op && checkRec(feF?.gL(), feS?.gL()) && checkRec(feF?.gR(), feS?.gR())) {
        true
    } else {
        if (feF?.stringView() ?: ";" != feS?.stringView() ?: "~") {
            throw Exception();
        }
        true
    }
}

fun get(code: Int?) = allData[code]
fun get(finalExpression: FinalExpression) = finalExpression.hashCode()

data class Data(
    var i: Int = 0,
    var last: Int = 0,
    var way: String = "",
    var mp1: Int = 0,
    var used: Boolean = false
)

fun fillAx(parser: FinalParser) {
    axiomas.addLast(use(parser.parse("A->B->A")))
    axiomas.addLast(use(parser.parse("(A->B)->(A->B->C)->(A->C)")))
    axiomas.addLast(use(parser.parse("A&B->A")))
    axiomas.addLast(use(parser.parse("A&B->B")))
    axiomas.addLast(use(parser.parse("A->B->A&B")))
    axiomas.addLast(use(parser.parse("A->A|B")))
    axiomas.addLast(use(parser.parse("B->A|B")))
    axiomas.addLast(use(parser.parse("(A->C)->(B->C)->(A|B->C)")))
    axiomas.addLast(use(parser.parse("(A->B)->(A->!B)->!A")))
    axiomas.addLast(use(parser.parse("!!A->A")))

    formalAxiomas.addLast(use(parser.parse("a=b->a=c->b=c")))
    formalAxiomas.addLast(use(parser.parse("a=b->a'=b'")))
    formalAxiomas.addLast(use(parser.parse("a'=b'->a=b")))
    formalAxiomas.addLast(use(parser.parse("!a'=0")))
    formalAxiomas.addLast(use(parser.parse("a+0=a")))
    formalAxiomas.addLast(use(parser.parse("a+b'=(a+b)'")))
    formalAxiomas.addLast(use(parser.parse("a*0=0")))
    formalAxiomas.addLast(use(parser.parse("a*b'=a*b+a")))
}


fun checkMainAx(): Boolean {
    for (i in axiomas.indices) {
        for (j in isWas.keys) isWas[j] = null
        isWas.clear()
        if (get(sentence)!!.weNeedAxiom(axiomas[i])) {
//            weDid[sentence] = Data(i + 1, size, AX)
            println("[$size. Ax. sch. ${i + 1}] ${sentence.getExp()!!.stringView()}")
            return true
        }
    }

    val sentenceExpr = get(sentence)
    if (checkElevenAx(sentenceExpr!!) || checkTvelweAx(sentenceExpr)) {
        return true
    }
    return checkANineAx()
}

fun checkTvelweAx(sentenceExpr: FinalExpression?): Boolean {
    if (sentenceExpr?.op != "->") return false
    if (sentenceExpr.gR()?.op != "?") return false

    val checker = varItisCount
    varItis = null
    allVariables.clear()
    if (!isItEqual(sentenceExpr.gR()!!.gL(), sentenceExpr.gR()!!.gR(), sentenceExpr.gL())) return false
    if (checker != varItisCount && varItis != null) findVars(varItis!!.getExp())
    if (allVariables.isEmpty() || !isSlave(sentenceExpr.gL())) {
        println("[$size. Ax. sch. 12] ${sentenceExpr.stringView()}")
        return true
    } else {
        println(
            "Expression $size: variable ${
            sentenceExpr.gR()!!.gL()
                ?.op
            } is not free for term ${varItis!!.getExp()!!.stringView()} in ?@-axiom."
        )
        stop = true
        exitProcess(0)
    }
}

var varItis: Int? = null
var varItisCount = 0
var allVariables: HashSet<String> = HashSet()
fun checkElevenAx(sentenceExpr: FinalExpression): Boolean {
    if (sentenceExpr.op != "->") return false
    if ((sentence.getExp()!!.gL()!!.op) != "@") return false
    varItis = null
    allVariables.clear()
    val checker = varItisCount
    if (!isItEqual(sentenceExpr.gL()!!.gL(), sentenceExpr.gL()!!.gR(), sentenceExpr.gR())) return false
    if (checker != varItisCount && varItis != null) findVars(varItis!!.getExp())
    if (allVariables.isEmpty() || !isSlave(sentenceExpr.gR())) {
        println("[$size. Ax. sch. 11] ${sentence.getExp()!!.stringView()}")
        return true
    } else {
        println(
            "Expression $size: variable ${sentenceExpr.gL()!!.gL()!!.op} is not free for term ${
            varItis!!.getExp()!!
                .stringView()
            } in ?@-axiom."
        )
        stop = true
        exitProcess(0)
    }
}

fun isSlave(ex: FinalExpression?): Boolean {
    return when (getExpressionType(ex)) {
        FinalExpressionType.BinaryExpression -> isSlave(ex?.gL()) && isSlave(ex?.gR())
        FinalExpressionType.UnaryExpression -> isSlave(ex?.gL())
        FinalExpressionType.Predicate -> (ex?.l != null && allVariables.contains(ex.l!!.getExp()!!.op)) || isSlave(ex?.gR())
        FinalExpressionType.Variable -> !allVariables.contains(ex?.op)
        FinalExpressionType.EmptyExpression -> false
    }
}

fun findVars(exp: FinalExpression?) {
    when (getExpressionType(exp)) {
        FinalExpressionType.BinaryExpression -> {
            findVars(exp!!.gL())
            findVars(exp.gR())
        }
        FinalExpressionType.UnaryExpression -> findVars(exp!!.gL())
        FinalExpressionType.Predicate -> {
            if ((!allVariables.contains(exp!!.l!!.getExp()!!.op)).also { findVars(exp.gR()) }) allVariables.remove(exp.l!!.getExp()!!.op)
        }
        FinalExpressionType.Variable -> {
            if (exp!!.op != "0") allVariables.add(exp.op)
        }
        else -> {
        }
    }
}

fun Int.getExp() = allData[this]

fun isItEqual(enterVar: FinalExpression?, weCame: FinalExpression?, predVar: FinalExpression?): Boolean {
    return when (getExpressionType(weCame)) {
        FinalExpressionType.BinaryExpression -> {
            getExpressionType(predVar) == FinalExpressionType.BinaryExpression &&
                    weCame!!.op == predVar!!.op
                    && isItEqual(enterVar, weCame.gL(), predVar.gL())
                    && isItEqual(enterVar, weCame.gR(), predVar.gR())
        }
        FinalExpressionType.UnaryExpression -> {
            getExpressionType(predVar) == FinalExpressionType.UnaryExpression &&
                    weCame!!.op == predVar!!.op
                    && isItEqual(enterVar, weCame.gL(), predVar.gL())
        }
        FinalExpressionType.Predicate -> {
            getExpressionType(predVar) == FinalExpressionType.Predicate &&
                    weCame!!.op == predVar!!.op
                    && (weCame.equals(predVar)
                    || (!weCame.gL()!!.equals(enterVar) && isItEqual(enterVar, weCame.gR(), predVar.gR())))
        }
        FinalExpressionType.Variable -> {
            if (weCame!!.op == enterVar?.op) {
                if (varItis == null) {//
                    varItis = get(predVar!!).also { varItisCount++ }
                    true
                } else {
                    predVar!!.equals(get(varItis))
                }
            } else {
                predVar?.equals(weCame) ?: false

            }
        }
        FinalExpressionType.EmptyExpression -> true
    }
}

fun getExpressionType(expr: FinalExpression?): FinalExpressionType {
    if (expr == null) return FinalExpressionType.EmptyExpression
    if (expr.l == null) return FinalExpressionType.Variable
    if (expr.r == null) return FinalExpressionType.UnaryExpression
    if (expr.op == "@" || expr.op == "?") return FinalExpressionType.Predicate
    return FinalExpressionType.BinaryExpression
}

fun checkFormalAx(): Boolean {
    for (i in formalAxiomas.indices) {
        if (get(sentence)!!.equals(formalAxiomas[i].getExp())) {
            println("[$size. Ax. A${i + 1}] ${sentence.getExp()!!.stringView()}")
            return true
        }
    }
    return false
}

fun checkANineAx(): Boolean {
    varItis = use(FinalExpression("0", null, null))
    val sentenceExpr = sentence.getExp()
    if (sentenceExpr?.op != "->"
        || sentenceExpr.gL()?.op != "&"
        || sentenceExpr.gL()?.gR()?.op != "@"
        || (sentenceExpr.gL()!!.gR()?.gR()?.op ?: "") != "->"
        || !(sentenceExpr.gL()!!.gR()!!.gR()!!.gL()!!.equals(sentenceExpr.gR()))
        || !isItEqual(sentenceExpr.gL()!!.gR()?.gL(), sentenceExpr.gR()!!, sentenceExpr.gL()!!.gL())
        || (sentenceExpr.gL()!!.gR()!!.gR()!!.gR() == null).also {
            varItis = use(FinalExpression("'", sentenceExpr.gL()!!.gR()!!.l, null))
        }
        || !isItEqual(sentenceExpr.gL()!!.gR()!!.gL(), sentenceExpr.gR(), sentenceExpr.gL()!!.gR()!!.gR()!!.gR())
    ) return false
    println("[$size. Ax. sch. A9] ${sentenceExpr.stringView()}")
    return true
}

fun checkImpl(): Boolean {
    var number = -1
    var modusPonus: FinalExpression? = null
    if (implications.contains(sentence)) {
        implications[sentence]!!.forEach {
            if (weDid.containsKey(get(it)!!.l!!)) {
                if (weDid[get(it)!!.l!!]!!.last >= number) {
                    number = weDid[get(it)!!.l!!]!!.last
                    modusPonus = it.getExp()!!
                }
            }
        }
        if (number > -1) {
            println(
                "[$size. M.P. ${weDid[modusPonus!!.l]?.last}, ${weDid[get(modusPonus!!)]?.last}] ${
                sentence.getExp()!!
                    .stringView()
                }"
            )
            return true
        }
    }
    return false
}

fun secondCheck(): Boolean {
    for (i in axiomas.indices) {
        for (j in isWas.keys) isWas[j] = null
        if (get(sentence)!!.weNeedAxiom(axiomas[i])) {
            weDid[sentence] = Data(i + 1, size, AX)
            return true
        }
    }
    return false
}

fun thirdCheck(): Boolean {
    if (implications.contains(sentence)) {
        implications[sentence]!!.forEach {
            if (weDid.containsKey(get(it)!!.l!!)) {
                weDid[sentence] =
                    Data((get(it)!!.l!!), size, MP, it)
                return true
            }
        }
    }
    return false
}

fun adToImpl() {
    if (get(sentence)!!.op == "->") {
        if (!implications.containsKey(get(sentence)!!.r!!)) {
            implications[get(sentence)!!.r!!] = HashSet()
        }
        implications[get(sentence)!!.r!!]!!.add(sentence)
    }
}

var isWas: HashMap<String, FinalExpression?> = HashMap()

/*
|-a+0=a
(((a)+0))=a
(@y.y+0*0'=y)->(?x.@y.x=y)


 */

/*
|-A->W->A
A->B->A&B
A->A|B
(A->P)->(B->P)->(A|B->P)
(@a.a+0=a)->b+0=b
0=0->(?x.x=0)
a=b->a=c->b=c
a=b->a'=b'
a'=b'->a=b
0=0&(@x.x=x->x'=x')->x=x
A->W->A

 */
/*
*/

/*
|- A -> A
A & A -> A
A -> A -> A
A -> (A -> A) -> A
A & A -> A
(A -> A -> A) -> (A -> (A -> A) -> A) -> A -> A
(A -> (A -> A) -> A) -> A -> A
A & A -> A
A -> A
 */
/*
(A -> B), !B |- !A
A -> B
!B
!B -> A -> !B
A -> !B
!B -> A -> !B
A -> !B
(A -> B) -> (A -> !B) -> !A
(A -> !B) -> !A
(A -> B) -> (A -> !B) -> !A
(A -> B) -> (A -> !B) -> !A
!B
!B -> A -> !B
A -> !B
!B
!B -> A -> !B
A -> !B
!B
!B -> A -> !B
A -> !B
!B
!B -> A -> !B
A -> !B
!B
!B -> A -> !B
A -> !B
!B
!B -> A -> !B
A -> !B
!B
!B
!B
!A
 */
/*
X, X->Y, Y->W, W->Y |- Y
Y -> W
W -> Y
X
X -> Y
Y
finishIt
 */
/*
A->(B->A), A, B |- A
A->(B->A)
B->AA->(B->A), A, B |- A
A->(B->A)
B->A
 */
