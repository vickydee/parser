/* #include <iostream>
#include <cstdio>
#include <cstdlib>
*/
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>
#include "lexer.h" // Token, LexicalAnalyzer

using namespace std;

struct Rule {
    string lhs;
    vector<string> rhs; 
};

/* KEY:
 * NT - nonterminals
 * T - terminals
 */
vector<Rule> grammarRules;
vector<string> lhsNTSorted;
vector<string> NTSorted;
vector<string> TSorted;
vector<string> symbolOrder;
map<string, int> NTOrder;
map<string, int> TOrder;
set<string> NTSet;
set<string> hasSym;
LexicalAnalyzer lexer;

// used 4 parsing 
void syntaxError() {
    cout << "SYNTAX ERROR !!!!!!!!!!!!!!\n";
    exit(1);
}

// symbol is NT iff LHS
bool isNT(const string& symbol) {
    return NTSet.find(symbol) != NTSet.end();
}
// helper method; checks token type
Token expect(TokenType expected) {
    Token token = lexer.GetToken();
    if (token.token_type != expected) {
        syntaxError();
    }
    return token;
}
// NT ordering 
void addLhsNT (const string& symbol) {
    if (NTSet.insert(symbol).second) { lhsNTSorted.push_back(symbol); }
}
// records every symbol first time it's seen
void addSym(const string& symbol) {
    if (hasSym.insert(symbol).second) {
        symbolOrder.push_back(symbol);
    }
}

/* after parsing finishes, split symbols into T and NT
 * cannot classify symbols safely until whole grammar is parsed
 * a symbol seen early on a RHS might appear later on some LHS
 * only after all LHS symbols are known can we correctly decide:
 * - in NTSet  => nonterminal
 * - otherwise => terminal
 * replaying symbolOrder at the end preserves first-appearance order
 * while still classifying every symbol correctly
 */
void refreshSymbolOrders() {
    NTSorted.clear();
    NTOrder.clear();
    TSorted.clear();
    TOrder.clear();
    for (const string& sym : symbolOrder) {
        if (isNT(sym)) {
            if (NTOrder.find(sym) == NTOrder.end()) {
                NTOrder[sym] = static_cast<int>(NTSorted.size());
                NTSorted.push_back(sym);
            }
        } else {
            if (TOrder.find(sym) == TOrder.end()) {
                TOrder[sym] = static_cast<int>(TSorted.size());
                TSorted.push_back(sym);
            }
        }
    }
}

/* e.g.  A -> x y | z | *
    *    =
    *    [x y], [z], []
    */
vector<vector<string>> parseRHS() {
    vector<vector<string>> rhsList;
    vector<string> currentRhs;

    while (true) {
        Token next = lexer.peek(1);
        if (next.token_type == STAR) {
            expect(STAR);
            rhsList.push_back(currentRhs);
            break;
        }
        if (next.token_type == OR) {
            expect(OR);
            rhsList.push_back(currentRhs);
            currentRhs.clear();
            continue;
        }
        if (next.token_type != ID) {
            syntaxError();
        }
        currentRhs.push_back(expect(ID).lexeme);
    }

    return rhsList;
}

map<string, bool> computeNullable() {
    map<string, bool> nullable;
    for (const string& nt : NTSorted) {
        nullable[nt] = false;
    }

    bool changed = true;
    while (changed) {
        // if this discovers at least one new nullable NT, another pass may unlock even more nullable symbols.
        changed = false;
        for (const Rule& rule : grammarRules) {
            bool allNullable = true;
            for (const string& symbol : rule.rhs) {
                // A terminal can never derive epsilon, so the whole RHS fails
                // immediately unless every symbol is a nullable nonterminal
                if (!isNT(symbol) || !nullable[symbol]) {
                    allNullable = false;
                    break;
                }
            }
            if (allNullable && !nullable[rule.lhs]) {
                nullable[rule.lhs] = true;
                changed = true;
            }
        }
    }

    return nullable;
}

map<string, set<string>> computeFirstSets(const map<string, bool>& nullable)
{
    // FIRST(A) is the set of terminals that can begin a string derived from A.
    //
    // For A -> X1 X2 ...:
    // - add X1 directly if it is a terminal
    // - otherwise add FIRST(X1)
    // - if X1 is nullable, continue to X2, etc.
    //
    // We keep iterating until a full pass adds nothing new.
    map<string, set<string>> first;
    for (const string& nt : NTSorted) {
        first[nt] = {};
    }

    bool changed = true;
    while (changed) {
        // FIRST information can propagate through chains like A -> B, B -> C,
        // C -> a, so we iterate until the sets stop growing.
        changed = false;
        for (const Rule& rule : grammarRules) {
            for (const string& symbol : rule.rhs) {
                if (!isNT(symbol)) {
                    // The first terminal we encounter is the first terminal
                    // the production can produce, so we add it and stop.
                    if (first[rule.lhs].insert(symbol).second) {
                        changed = true;
                    }
                    break;
                }

                // If the next symbol is a nonterminal, inherit everything its
                // FIRST set already knows.
                size_t before = first[rule.lhs].size();
                first[rule.lhs].insert(first[symbol].begin(), first[symbol].end());
                if (first[rule.lhs].size() != before) {
                    changed = true;
                }

                // Once a non-nullable symbol appears, nothing after it can ever
                // become the first terminal of this production.
                if (!nullable.at(symbol)) {
                    break;
                }
            }
        }
    }

    return first;
}

set<string> firstOfSequence(
    const vector<string>& sequence,
    size_t start_index,
    const map<string, bool>& nullable,
    const map<string, set<string>>& first)
{
    // FOLLOW repeatedly needs FIRST(beta) where beta is the suffix after a
    // nonterminal inside a production. This helper computes that suffix-FIRST.
    set<string> result;
    for (size_t i = start_index; i < sequence.size(); ++i) {
        const string& symbol = sequence[i];
        if (!isNT(symbol)) {
            // A terminal ends the search immediately.
            result.insert(symbol);
            return result;
        }

        // A nonterminal contributes all of its FIRST terminals.
        result.insert(first.at(symbol).begin(), first.at(symbol).end());
        if (!nullable.at(symbol)) {
            // If it is not nullable, the suffix cannot continue past it.
            return result;
        }
    }
    // If every remaining symbol is nullable, the suffix contributes no direct
    // terminal by itself; the caller handles the FOLLOW(LHS) case separately.
    return result;
}

map<string, set<string>> computeFollowSets(
    const map<string, bool>& nullable,
    const map<string, set<string>>& first)
{
    // FOLLOW(A) is the set of terminals that can appear immediately after A.
    //
    // For every A -> alpha B beta:
    // - FIRST(beta) goes into FOLLOW(B)
    // - if beta can disappear, FOLLOW(A) also goes into FOLLOW(B)
    //
    // Like nullable/FIRST, FOLLOW is solved by fixed-point iteration.
    map<string, set<string>> follow;
    for (const string& nt : NTSorted) {
        follow[nt] = {};
    }
    if (!NTSorted.empty()) {
        follow[NTSorted[0]].insert("$");
    }

    bool changed = true;
    while (changed) {
        // FOLLOW dependencies can be circular, so we again solve by repeated
        // propagation until no set changes.
        changed = false;
        for (const Rule& rule : grammarRules) {
            for (size_t i = 0; i < rule.rhs.size(); ++i) {
                const string& symbol = rule.rhs[i];
                if (!isNT(symbol)) {
                    continue;
                }

                set<string> seq_first = firstOfSequence(rule.rhs, i + 1, nullable, first);
                size_t before = follow[symbol].size();
                follow[symbol].insert(seq_first.begin(), seq_first.end());
                if (follow[symbol].size() != before) {
                    changed = true;
                }

                // Check whether everything after the current symbol can
                // disappear. If so, FOLLOW(LHS) must flow into FOLLOW(symbol).
                bool suffix_nullable = true;
                for (size_t j = i + 1; j < rule.rhs.size(); ++j) {
                    if (!isNT(rule.rhs[j]) || !nullable.at(rule.rhs[j])) {
                        suffix_nullable = false;
                        break;
                    }
                }
                if (i + 1 == rule.rhs.size()) {
                    suffix_nullable = true;
                }

                if (suffix_nullable) {
                    before = follow[symbol].size();
                    follow[symbol].insert(follow[rule.lhs].begin(), follow[rule.lhs].end());
                    if (follow[symbol].size() != before) {
                        changed = true;
                    }
                }
            }
        }
    }

    return follow;
}

string joinRhs(const vector<string>& rhs)
{
    // Convert a RHS into a single comparable string so sorting rules is easy.
    string joined;
    for (size_t i = 0; i < rhs.size(); ++i) {
        if (i > 0) {
            joined += " ";
        }
        joined += rhs[i];
    }
    return joined;
}

bool ruleSortLess(const Rule& a, const Rule& b)
{
    // The transformation tasks are graded against deterministic output.
    // Sort by LHS name, then by RHS text, with epsilon first for the same LHS.
    if (a.lhs != b.lhs) {
        return a.lhs < b.lhs;
    }
    if (a.rhs.empty() != b.rhs.empty()) {
        return a.rhs.empty();
    }
    return joinRhs(a.rhs) < joinRhs(b.rhs);
}

void printGrammar(const vector<Rule>& rules)
{
    // Print transformed grammars in sorted order so the output is predictable
    // and matches the expected answer files exactly.
    vector<Rule> sorted_rules = rules;
    sort(sorted_rules.begin(), sorted_rules.end(), ruleSortLess);
    for (const Rule& rule : sorted_rules) {
        cout << rule.lhs << " ->";
        if (!rule.rhs.empty()) {
            cout << " ";
            for (size_t i = 0; i < rule.rhs.size(); ++i) {
                if (i > 0) {
                    cout << " ";
                }
                cout << rule.rhs[i];
            }
        }
        cout << " #\n";
    }
}

vector<Rule> leftFactorGrammar()
{
    // Left factoring extracts the longest common prefix shared by two or more
    // productions of the same nonterminal.
    //
    // Example:
    //   A -> a b c
    //   A -> a b d
    // becomes:
    //   A  -> a b A1
    //   A1 -> c
    //   A1 -> d
    //
    // We repeatedly factor one best prefix at a time until no LHS has another
    // common prefix worth extracting.
    vector<Rule> rules = grammarRules;
    map<string, int> next_suffix;
    for (const string& nt : NTSorted) {
        next_suffix[nt] = 1;
    }

    bool changed = true;
    while (changed) {
        changed = false;
        vector<string> lhses;
        set<string> seen;
        for (const Rule& rule : rules) {
            if (seen.insert(rule.lhs).second) {
                lhses.push_back(rule.lhs);
            }
        }

        for (const string& lhs : lhses) {
            // Work on one nonterminal at a time because only productions with
            // the same LHS can be left-factored together.
            vector<Rule> group;
            for (const Rule& rule : rules) {
                if (rule.lhs == lhs) {
                    group.push_back(rule);
                }
            }

            size_t best_len = 0;
            vector<string> best_prefix;
            for (size_t i = 0; i < group.size(); ++i) {
                for (size_t j = i + 1; j < group.size(); ++j) {
                    // Measure the common prefix length of every pair and keep
                    // the longest one. That is the next factoring opportunity.
                    size_t prefix_len = 0;
                    while (prefix_len < group[i].rhs.size() &&
                           prefix_len < group[j].rhs.size() &&
                           group[i].rhs[prefix_len] == group[j].rhs[prefix_len]) {
                        ++prefix_len;
                    }
                    if (prefix_len > best_len) {
                        best_len = prefix_len;
                        best_prefix.assign(group[i].rhs.begin(), group[i].rhs.begin() + prefix_len);
                    }
                }
            }

            if (best_len == 0) {
                continue;
            }

            vector<Rule> matching;
            vector<Rule> remaining;
            for (const Rule& rule : group) {
                bool has_prefix = rule.rhs.size() >= best_len;
                for (size_t i = 0; has_prefix && i < best_len; ++i) {
                    if (rule.rhs[i] != best_prefix[i]) {
                        has_prefix = false;
                    }
                }
                if (has_prefix) {
                    // These rules will be replaced by the new factored form.
                    matching.push_back(rule);
                } else {
                    // These rules stay unchanged for this LHS.
                    remaining.push_back(rule);
                }
            }

            if (matching.size() < 2) {
                continue;
            }

            string new_lhs = lhs + to_string(next_suffix[lhs]++);
            vector<Rule> updated;
            for (const Rule& rule : rules) {
                if (rule.lhs != lhs) {
                    updated.push_back(rule);
                }
            }

            for (const Rule& rule : remaining) {
                updated.push_back(rule);
            }

            Rule factored_rule;
            factored_rule.lhs = lhs;
            factored_rule.rhs = best_prefix;
            factored_rule.rhs.push_back(new_lhs);
            updated.push_back(factored_rule);

            for (const Rule& rule : matching) {
                // The helper nonterminal stores only the suffix that remains
                // after removing the extracted common prefix.
                Rule suffix_rule;
                suffix_rule.lhs = new_lhs;
                suffix_rule.rhs.assign(rule.rhs.begin() + best_len, rule.rhs.end());
                updated.push_back(suffix_rule);
            }

            rules = updated;
            changed = true;
            break;
        }
    }

    return rules;
}

vector<Rule> eliminateLeftRecursion()
{
    // The expected project output uses lexicographic order of the original
    // nonterminals for left-recursion elimination, so we sort them here.
    vector<string> originalNTs = lhsNTSorted;
    sort(originalNTs.begin(), originalNTs.end());

    map<string, vector<vector<string>>> productions;
    for (const string& nt : originalNTs) {
        productions[nt] = {};
    }
    for (const Rule& rule : grammarRules) {
        productions[rule.lhs].push_back(rule.rhs);
    }

    vector<string> order = originalNTs;
    vector<string> output_order = originalNTs;
    map<string, int> next_suffix;
    for (const string& nt : order) {
        next_suffix[nt] = 1;
    }

    size_t original_count = order.size();
    for (size_t i = 0; i < original_count; ++i) {
        const string ai = order[i];

        // First remove indirect left recursion through earlier nonterminals.
        // If Ai starts with Aj and j < i, substitute Aj's productions into Ai.
        for (size_t j = 0; j < i; ++j) {
            const string aj = order[j];
            vector<vector<string>> expanded;
            for (const vector<string>& rhs : productions[ai]) {
                if (!rhs.empty() && rhs[0] == aj) {
                    // Replace Ai -> Aj gamma with every possible Aj production
                    // followed by the original suffix gamma.
                    vector<string> suffix(rhs.begin() + 1, rhs.end());
                    for (const vector<string>& aj_rhs : productions[aj]) {
                        vector<string> replacement = aj_rhs;
                        replacement.insert(replacement.end(), suffix.begin(), suffix.end());
                        expanded.push_back(replacement);
                    }
                } else {
                    expanded.push_back(rhs);
                }
            }
            productions[ai] = expanded;
        }

        vector<vector<string>> alpha;
        vector<vector<string>> beta;
        for (const vector<string>& rhs : productions[ai]) {
            // Separate direct-left-recursive productions:
            //   Ai -> Ai alpha   goes to alpha
            //   Ai -> beta       goes to beta
            if (!rhs.empty() && rhs[0] == ai) {
                alpha.emplace_back(rhs.begin() + 1, rhs.end());
            } else {
                beta.push_back(rhs);
            }
        }

        if (alpha.empty()) {
            // No direct left recursion for this nonterminal, so nothing to fix.
            continue;
        }

        string new_nt = ai + to_string(next_suffix[ai]++);
        output_order.push_back(new_nt);
        productions[new_nt] = {};

        // Standard rewrite:
        //   Ai  -> beta Ai'
        //   Ai' -> epsilon | alpha Ai'
        //
        // New helper nonterminals are added to the output, but they are not fed
        // back into the outer elimination loop. Only original nonterminals are
        // processed by the ordered algorithm.
        vector<vector<string>> new_ai;
        for (const vector<string>& rhs : beta) {
            vector<string> updated_rhs = rhs;
            updated_rhs.push_back(new_nt);
            new_ai.push_back(updated_rhs);
        }
        productions[ai] = new_ai;

        // Epsilon production: Ai' can stop after consuming zero alpha blocks.
        productions[new_nt].push_back({});
        for (const vector<string>& rhs : alpha) {
            vector<string> updated_rhs = rhs;
            updated_rhs.push_back(new_nt);
            productions[new_nt].push_back(updated_rhs);
        }
    }

    vector<Rule> result;
    for (const string& lhs : output_order) {
        for (const vector<string>& rhs : productions[lhs]) {
            result.push_back({lhs, rhs});
        }
    }
    return result;
}

void printOrderedSymbolSet(const set<string>& symbols, bool include_dollar)
{
    // Utility for deterministic set printing using the project's terminal order.
    bool first_output = true;
    if (include_dollar && symbols.find("$") != symbols.end()) {
        cout << "$";
        first_output = false;
    }
    for (const string& terminal : TSorted) {
        if (symbols.find(terminal) == symbols.end()) {
            continue;
        }
        if (!first_output) {
            cout << ", ";
        }
        cout << terminal;
        first_output = false;
    }
}
void readGrammar()
{
    // Parse the grammar once and build all metadata needed by every task:
    // - one Rule per production alternative
    // - original LHS nonterminal order
    // - first-appearance order of all symbols
    grammarRules.clear();
    lhsNTSorted.clear();
    NTSorted.clear();
    TSorted.clear();
    symbolOrder.clear();
    NTOrder.clear();
    TOrder.clear();
    NTSet.clear();
    hasSym.clear();

    while (lexer.peek(1).token_type != HASH) {
        Token lhs = expect(ID);
        addSym(lhs.lexeme);
        addLhsNT(lhs.lexeme);
        expect(ARROW);
        vector<vector<string>> rhsList = parseRHS();
        for (const vector<string>& rhs : rhsList) {
            for (const string& symbol : rhs) {
                addSym(symbol);
            }
            grammarRules.push_back({lhs.lexeme, rhs});
        }
    }
    expect(HASH);
    refreshSymbolOrders();
}

/* 
 * Task 1: 
 * Printing the terminals, then nonterminals of grammar in appearing order
 * output is one line, and all names are space delineated
*/
void Task1()
{
    for (const string& terminal : TSorted) {
        cout << terminal << " ";
    }
    for (const string& nonterminal : NTSorted) {
        cout << nonterminal << " ";
    }
    cout << "\n";
}

/*
 * Task 2:
 * Print out nullable set of the grammar in specified format.
*/
void Task2()
{
    map<string, bool> nullable = computeNullable();
    // The exact spacing here matters because the tests compare formatting.
    cout << "Nullable = {";
    bool first = true;
    for (const string& nt : NTSorted) {
        if (!nullable[nt]) {
            continue;
        }
        cout << (first ? " " : " , ");
        cout << nt;
        first = false;
    }
    cout << " }\n";
}

// Task 3: FIRST sets
void Task3()
{
    map<string, bool> nullable = computeNullable();
    map<string, set<string>> first = computeFirstSets(nullable);

    // Print nonterminals in grammar appearance order and terminals inside each
    // set in terminal appearance order to match the expected output format.
    for (const string& nt : NTSorted) {
        cout << "FIRST(" << nt << ") = { ";
        printOrderedSymbolSet(first[nt], false);
        cout << " }\n";
    }
}

// Task 4: FOLLOW sets
void Task4()
{
    map<string, bool> nullable = computeNullable();
    map<string, set<string>> first = computeFirstSets(nullable);
    map<string, set<string>> follow = computeFollowSets(nullable, first);

    // FOLLOW uses the same deterministic terminal order as FIRST, except that
    // $ is printed first because it is not one of the grammar terminals.
    for (const string& nt : NTSorted) {
        cout << "FOLLOW(" << nt << ") = { ";
        printOrderedSymbolSet(follow[nt], true);
        cout << " }\n";
    }
}

// Task 5: left factoring
void Task5()
{
    printGrammar(leftFactorGrammar());
}

// Task 6: eliminate left recursion
void Task6()
{
    printGrammar(eliminateLeftRecursion());
}
    
int main (int argc, char* argv[])
{
    int task;

    if (argc < 2)
    {
        cout << "Error: missing argument\n";
        return 1;
    }

    /*
       Note that by convention argv[0] is the name of your executable,
       and the first argument to your program is stored in argv[1]
     */

    task = atoi(argv[1]);
    
    readGrammar();  // Reads the input grammar from standard input
                    // and represent it internally in data structures
                    // ad described in project 2 presentation file

    switch (task) {
        case 1: Task1();
            break;

        case 2: Task2();
            break;

        case 3: Task3();
            break;

        case 4: Task4();
            break;

        case 5: Task5();
            break;
        
        case 6: Task6();
            break;

        default:
            cout << "Error: unrecognized task number " << task << "\n";
            break;
    }
    return 0;
}



