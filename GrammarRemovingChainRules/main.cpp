#include <QString>
#include <QVector>
#include <QtDebug>

QString empty = "X";

struct Symbol
{
    Symbol() : str(empty) {}
    explicit Symbol(const QString &str) : str(str) { Q_ASSERT(str != empty); } // kirrilean e
    inline QString s() const { return str; }
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

struct Grammar
{
    Grammar() = default;
    SymbolsSet vt;
    SymbolsSet vn;
    QVector<Rule> p;
    Symbol s;
    inline void print() const
    {
        qDebug() << "";
        qDebug() << "VT" << vt;
        qDebug() << "VN" << vn;
        qDebug() << "P" << p;
        qDebug() << "S" << s;
    }
};

SymbolsSet sigmaSet(const Grammar &g, const Symbol &vn) {
    const SymbolsSet vns = g.vn;
    Q_ASSERT(vns.contains(vn));

    SymbolsSet res = {vn};
    int nAdded = 0;
    do {
        nAdded = 0;
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
    } while (nAdded);
    return res;
}

Grammar removeChainRules(const Grammar &g) {
    qDebug() << "sigma sets:";
    QVector<SymbolsSet> sigmaSets;
    for (const Symbol &vn : g.vn){
        qDebug() << vn << "\t" << sigmaSet(g, vn);
        sigmaSets << sigmaSet(g, vn);
    }

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
                for (const Symbol &s : otherSymbolsWhichContainThis)
                    rulesToAdd << Rule(s, rule.r);
            }
    }
    qDebug() << "to skip:" << rulesToSkip;
    qDebug() << "to add:" << rulesToAdd;
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

int main()
{
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

    return 0;
}
