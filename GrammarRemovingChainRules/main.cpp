#include <QString>
#include <QVector>
#include <QHash>
#include <iostream>

QString empty = "empty";

struct Symbol
{
    Symbol() : str(empty) {}
    explicit Symbol(const QString &str) : str(str) { Q_ASSERT(str != empty); } // kirrilean e
    inline QString s() const { return str; }
    inline bool operator<(const Symbol &other) const { return str < other.str; }
    inline bool operator==(const Symbol &other) const { return str == other.str; }
    inline operator QString() const { return s();}
    inline bool isEmpty() const { return str == empty; }
    QString str;

};

using SymbolsSet = QVector<Symbol>;

struct Chain
{
    Chain() = default;
    Chain(const Symbol &symbol) : symbols({symbol}) {}
    Chain(const QVector<Symbol> &symbols) : symbols(symbols) {}
    inline operator QString() const { return s();}
    inline bool operator==(const Chain &other) const { return symbols == other.symbols; }
    inline QString s() const
    {
        QString res;
        for (const Symbol &symbol : symbols)
            res += symbol.s();
        return res.isEmpty() ? empty : res;

    }
    inline int length() const { return symbols.size(); }
    inline Symbol left() const  { return length() ? symbols.first() : Symbol(empty); }
    inline Symbol right() const  { return length() ? symbols.last() : Symbol(empty); }
    QVector<Symbol> symbols;
};

struct Rule
{
    Rule() = default;
    Rule(const Symbol &l, const Chain &r) : l(l), r(r) {}
    Symbol l;
    Chain r;
    inline QString s() const
    {
        return QString("%1 -> %2").arg(l.s()).arg(r.s());
    }
    inline operator QString() const { return s();}
    inline bool operator==(const Rule &other) const { return l == other.l and r == other.r; }
};


template <typename T>
void printVector(const QVector<T> &vec)
{
    if (vec.isEmpty()) {
        std::cout << empty.toStdString();
    }
    std::cout << "{ ";
    int ind = 0;
    for (const T &t : vec) {
        const QString s = t;
        if (ind)
            std::cout << ", ";
        std::cout << s.toStdString();
        ++ind;
    }
    std::cout << " }";
}

void printRules(const QVector<Rule> &rules)
{
    QHash<Symbol, QVector<Chain>> res;
    for (const Rule &rule : rules) {
        res[rule.l].append(rule.r);
    }
    std::cout << "{";
    int ind = 0;
    QList<Symbol> keys = res.keys();
    std::sort(keys.begin(), keys.end());
    for (const Symbol &s : keys) {
        if (ind)
            std::cout << ",";
        std::cout << std::endl << "  " << s.s().toStdString() << " -> ";
        int chainInd = 0;
        for (const Chain &chain : res[s]) {
            if (chainInd)
                std::cout << " | ";
            std::cout << chain.s().toStdString();
            ++chainInd;
        }
        ++ind;
    }
    std::cout  << std::endl << "}";

}

struct Grammar
{
    Grammar() = default;
    SymbolsSet vt;
    SymbolsSet vn;
    QVector<Rule> p;
    Symbol s;
    inline void print() const
    {
        std::cout << std::endl;
        std::cout << "V_T = ";
        printVector(vt);
        std::cout << std::endl;
        std::cout << "V_N = ";
        printVector(vn);
        std::cout << std::endl;
        std::cout << "P = ";
        printRules(p);
        std::cout << std::endl;
        std::cout << "S = " << s.s().toStdString() << std::endl;

    }
};
/// sigma A = {B | A => *B}
/// input Grammar G (V_T, V_N, P, S), no Empty rules, and A in V_N
SymbolsSet sigmaSet(const Grammar &g, const Symbol &a) {
    const SymbolsSet vns = g.vn;
    Q_ASSERT(vns.contains(a));

    /// 1. sigma_A_0 = {A}
    SymbolsSet res = {a};
    int nAdded = 0;
    do {
        nAdded = 0;
        /// 2. sigma_A_i << {C | (B->C) in P, B in sigma_A-1}
        for (const Rule &rule : g.p) {
            const Symbol l = rule.l;
            if (not res.contains(l))
                continue;
            const Chain rchain = rule.r;
            const bool isChainOne = rchain.length() == 1;
            if (not isChainOne)
                continue;
            const Symbol r = rchain.left();
            const bool isNonTerm = vns.contains(r);
            if (not isNonTerm)
                continue;
            if (r == l or res.contains(r))
                continue;
            res << r;
            ++nAdded;
        }
        /// when no added, means
        /// 3. sigma_A_i == sigma_A_i-1 -> finish
        /// else move to 2.
    } while (nAdded);
    /// 4. sigma_A = sigma_A_i
    return res;
}

/// Алгоритм исключения цепных правил заключается в том,
/// что левые части правил заменяются нетерминальными символами,
/// которые выводятся из цепных правил.
/// input Grammar G (V_T, V_N, P, S), no Empty rules, and A in V_N
Grammar removeChainRules(const Grammar &g) {
    std::cout << "sigma sets:" << std::endl;
    QVector<SymbolsSet> sigmaSets;
    /// for each A in V_N get sigma_A = {B | A=>*B}
    for (const Symbol &vn : g.vn){
        std::cout << vn.s().toStdString() << "  ";
        printVector(sigmaSet(g, vn));
        std::cout << std::endl;
        sigmaSets << sigmaSet(g, vn);
    }


    /// all (B->lambda) in P change for (A->lambda) for each A i.e. B in sigma_A
    QVector<Rule> rulesToSkip;
    QVector<Rule> rulesToAdd;
    const int n = g.vn.size();
    for (int i = 0; i < n; ++i) {
        const Symbol l = g.vn[i];
        const SymbolsSet sigmaSet = sigmaSets[i];
        for (const Symbol &s : sigmaSet) {
            if (l == s)
                continue;
            rulesToSkip << Rule(l, s);
        }
        SymbolsSet otherSymbolsWhichContainThis;
        for (int j  = 0; j < n; ++j) {
            if (i == j or not sigmaSets[j].contains(l))
                continue;
            otherSymbolsWhichContainThis << g.vn[j];
        }
        for (const Rule &rule : g.p)
            if (rule.l == l) {
                if (rule.r.length() == 1 and g.vn.contains(rule.r.left()))
                    continue;
                for (const Symbol &s : otherSymbolsWhichContainThis) {
                    Rule toAdd(s, rule.r);
                    rulesToAdd << toAdd;
                }
            }
    }
    std::cout << "to skip = ";
    printRules(rulesToSkip);
    std::cout << std::endl;
    std::cout << "to add = ";
    printRules(rulesToAdd);
    std::cout << std::endl;
    QVector<Rule> p2;
    for (const Rule &rule : g.p) {
        if (rulesToSkip.contains(rule))
            continue;
        p2 << rule;
    }
    p2 << rulesToAdd;
    Grammar g2 = g;
    g2.p = p2;
    return g2;
}

void example()
{
    Symbol a("a");
    Symbol b("b");
    Symbol c("c");

    Symbol A("A");
    Symbol B("B");
    Symbol C("C");
    Symbol S("S");

    Grammar g;
    g.vt = { a, b, c };
    g.vn = { A, B, C, S };
    g.p = {
        Rule(S, Chain({B, A})),
        Rule(A, Chain(C)),
        Rule(A, Chain({a, c})),
        Rule(B, Chain(b)),
        Rule(C, Chain(A)),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

void task7a()
{
    Symbol colomn(":");
    Symbol equals("=");
    Symbol open("(");
    Symbol close(")");
    Symbol i("i");

    Symbol A("A");
    Symbol B("B");
    Symbol L("L");
    Symbol P("P");
    Symbol F("F");
    Symbol Q("Q");
    Symbol S("S");

    Grammar g;
    g.vt = { i, colomn, equals, open, close};
    g.vn = { A, B, L, P, F, Q, S };
    g.p = {
        Rule(S, Chain({L, A})),
        Rule(S, Chain({L, B})),
        Rule(L, Chain({P, colomn, equals})),
        Rule(L, Chain({Q, colomn, equals})),
        Rule(P, Chain(i)),
        Rule(A, Chain(F)),
        Rule(Q, Chain(i)),
        Rule(B, Chain(F)),
        Rule(F, Chain({Q, open, i, close})),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

void task7b()
{
    Symbol a("a");
    Symbol i("i");

    Symbol A("A");
    Symbol B("B");
    Symbol C("C");
    Symbol D("D");
    Symbol S("S");

    Grammar g;
    g.vt = { a, i };
    g.vn = { A, B, C, D, S };
    g.p = {
        Rule(S, Chain({A, C})),
        Rule(A, Chain(B)),
        Rule(A, Chain({A, a, B})),
        Rule(B, Chain(i)),
        Rule(C, Chain(D)),
        Rule(C, Chain({D, a, C})),
        Rule(D, Chain(i)),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

void task7c()
{
    Symbol one("1");
    Symbol zero("0");

    Symbol A("A");
    Symbol B("B");
    Symbol C("C");
    Symbol S("S");

    Grammar g;
    g.vt = { one, zero };
    g.vn = { A, B, C, S };
    g.p = {
        Rule(S, Chain({one, A})),
        Rule(S, Chain({B, zero})),
        Rule(A, Chain({one, A})),
        Rule(A, Chain(C)),
        Rule(B, Chain({B, zero})),
        Rule(B, Chain(C)),
        Rule(C, Chain({one, C, zero})),
        Rule(C, Chain()),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

void task7d()
{
    Symbol plus("+");
    Symbol mult("*");
    Symbol i("i");

    Symbol P("P");
    Symbol T("T");
    Symbol S("S");

    Grammar g;
    g.vt = { plus, mult, i };
    g.vn = { P, T, S };
    g.p = {
        Rule(S, Chain({T, plus, P})),
        Rule(S, Chain(T)),
        Rule(T, Chain({T, mult, P})),
        Rule(T, Chain(P)),
        Rule(P, Chain(i)),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

void task7e()
{
    Symbol one("1");
    Symbol zero("0");
    Symbol a("a");
    Symbol b("b");


    Symbol A("A");
    Symbol B("B");
    Symbol S("S");

    Grammar g;
    g.vt = { one, zero, a, b };
    g.vn = { A, B, S };
    g.p = {
        Rule(S, Chain(A)),
        Rule(S, Chain(B)),
        Rule(A, Chain({one, A, zero})),
        Rule(A, Chain({one, a, zero})),
        Rule(B, Chain({one, B, zero, zero})),
        Rule(B, Chain({one, b, zero, zero})),
    };
    g.s = S;
    g.print();
    Grammar g2 = removeChainRules(g);
    g2.print();
}

int main()
{
    using namespace std;
    cout << endl << "------------ example" << endl;
    example();
    cout << endl << "------------ 7 a)" << endl;
    task7a();
    cout << endl << "------------ 7 b)" << endl;
    task7b();
    cout << endl << "------------ 7 c)" << endl;
    task7c();
    cout << endl << "------------ 7 d)" << endl;
    task7d();
    cout << endl << "------------ 7 e)" << endl;
    task7e();
}
