struct Rule {
    string lhs;
    vector<string> rhs; 
};

vector<Rule> rules;
vector<string> nonterminals_in_order;
vector<string> symbols_in_order;
unordered_set<string> nonterminal_set;
unordered_set<string> symbol_seen;
unordered_map<string, vector<vector<string>>> grouped;
string start_symbol;

vector<string> terminals_in_order;
for (string s : symbols_in_order) {
    if (!nonterminal_set.count(s)) terminals_in_order.push_back(s);
}

parse_grammar()
 
parse_rule()

parse_one_rhs()
