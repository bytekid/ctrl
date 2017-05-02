#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
using namespace std;

#define REFERENCES_PATH     "references/"
#define SPECIFICATIONS_PATH "specifications/"

struct EquivalenceInfo {
  string fun1;
  string fun2;
  string constraint;
  EquivalenceInfo(string f, string g, string c)
    : fun1(f), fun2(g), constraint(c) {}
};

struct SpecificationInfo {
  vector<string> extra_symbs;
  vector<string> extra_declarations;
  vector<string> extra_rules;
  string mainfun;
  string equation;
  SpecificationInfo(string fun, string eq) :mainfun(fun), equation(eq) {}
};

vector<string> lines;   // lines in the input file(s)
EquivalenceInfo *equiv_info;
SpecificationInfo *spec_info;

/*****************************************************************************/
/*                                STRING FUNCTIONS                           */
/*****************************************************************************/

// removes starting and ending whitespace from the given string
string trim(string str) {
  size_t i = str.find_first_not_of(" \t");
  size_t j = str.find_last_not_of(" \t");
  if (i != string::npos && j != string::npos)
    return str.substr(i,j-i+1);
  return "";
}

// returns the part of string starting from the nth "word" (space-separated)
// we start indexing from 1
string words_from(string str, int n) {
  size_t p = 0;
  for (int k = 1; k < n; k++) {
    p = str.find(' ', p);
    if (p == string::npos) return "";
    p = str.find_first_not_of(" \t", p);
  }
  return str.substr(p);
}

// returns the nth "word" (whitespace-separated) in the string
// starting from 1
string word(string str, int n) {
  string start = words_from(str, n);
  size_t p = start.find(' ');
  if (p == string::npos) return start;
  else return start.substr(0, p);
}

// replaces all occurrences of "str" in source by "by"
string replace_all(string source, string str, string by) {
  string done = "";
  while (true) {
    size_t k = source.find(str);
    if (k == string::npos) return done + source;
    done += source.substr(0, k) + by;
    source = source.substr(k + str.length());
  }
}

/*****************************************************************************/
/*                             SAVING AND LOADING                            */
/*****************************************************************************/

// appends the contents of the given filename fo lines, provided it loads
// if the file doesn't load, gives a warning if warn is true
void load_file(string filename, bool warn) {
  string line;
  ifstream f(filename.c_str());
  if (!f.is_open()) {
    if (warn) cout << "Could not read file: " << filename << endl;
    return;
  }
  while (getline(f, line)) {
    lines.push_back(line);
  }
}

// write the contents of lines, starting from line start, to the given file
void write_merged_file(string filename, int start) {
  ofstream f(filename.c_str());
  for (int i = start; i < lines.size(); i++) {
    f << lines[i] << endl;
  }
  f.close();
}

/*****************************************************************************/
/*                       READING AND PARSING THE QUERY                       */
/*****************************************************************************/

// reads a trimmed line that should contain the query
string read_query(string line) {
  if (line.substr(0,3) == "/**" && line.substr(line.length()-2,2) == "*/") {
    return trim(line.substr(3,line.length()-5));
  }
  if (line.substr(0,2) == "/*" && line.substr(line.length()-2,2) == "*/") {
    return trim(line.substr(2,line.length()-4));
  }
  else if (line.substr(0,2) == "//") {
    return trim(line.substr(2));
  }
  return "";
}

// parses the query into the global variables
bool parse_query(string query) {
  // initialisation
  equiv_info = NULL;
  spec_info = NULL;
  // parse the query we read
  string request = word(query, 1);
  
  // equivalence query
  if (request == "equivalence" || request == "EQUIVALENCE") {
    string fun1 = word(query, 2);
    string fun2 = word(query, 3);
    string constraints = words_from(query, 4);
    equiv_info = new EquivalenceInfo(fun1, fun2, constraints);
    return true;
  }

  // correspondence query
  if (request == "specification" || request == "SPECIFICATION") {
    string mainfun = word(query, 2);
    string equation = words_from(query, 3);
    spec_info = new SpecificationInfo(mainfun, equation);
    return true;
  }

  return false;
}

/*****************************************************************************/
/*                            UNIFYING TYPE NAMES                            */
/*****************************************************************************/

// gives f the basic "result" output type
void replace_main_name(string f) {
  for (int i = 0; i < lines.size(); i++) {
    lines[i] = replace_all(lines[i], "result_" + f + ";", "result;");
    lines[i] = replace_all(lines[i], "result_" + f + " ", "result ");
    lines[i] = replace_all(lines[i], "err_" + f + ":", "error:");
    lines[i] = replace_all(lines[i], "err_" + f + " ", "error ");
    lines[i] = replace_all(lines[i], "err_" + f + ",", "error,");
    lines[i] = replace_all(lines[i], "err_" + f + ")", "error)");
    lines[i] = replace_all(lines[i], "err_" + f + ";", "error;");
    lines[i] = replace_all(lines[i], "ret_" + f + ":", "return:");
    lines[i] = replace_all(lines[i], "ret_" + f + " ", "return ");
    lines[i] = replace_all(lines[i], "ret_" + f + ",", "return,");
    lines[i] = replace_all(lines[i], "ret_" + f + "(", "return(");
    lines[i] = replace_all(lines[i], "ret_" + f + ")", "return)");
    lines[i] = replace_all(lines[i], "ret_" + f + ";", "return;");
  }
}

/*****************************************************************************/
/*                     FUNCTIONS FOR LCTRS SPECIFICATIONS                    */
/*****************************************************************************/

// adds the given declaration to the signature saved in "lines"
void add_to_signature(string declaration) {
  for (int i = 0; i < lines.size(); i++) {
    if (lines[i] == "SIGNATURE") {
      lines.insert(lines.begin() + i + 1, declaration);
      return;
    }
  }
}

// adds the given rule to the rules saved in "lines"
void add_to_rules(string rule) {
  for (int i = 0; i < lines.size(); i++) {
    if (lines[i] == "RULES") {
      lines.insert(lines.begin() + i + 1, rule);
      return;
    }
  }
}

// this is called *after* a specification file has been read into lines
void read_specification_file() {
  // TODO
}

// main function for the specification case
string handle_specification() {
  // TODO
  return "";
}

/*****************************************************************************/
/*               FUNCTIONS FOR EQUIVALENCE BETWEEN C-FUNCTIONS               */
/*****************************************************************************/

// changes the query for the equivalence problem where f and g have
// the given declaration
void fix_equivalence_query(string f, string g, string declaration) {
  string varstring = "";
  size_t p = 0;
  int i;

  if (declaration.find("=>") != string::npos) {
    int arity = 1;
    varstring = "x1";
    while ((p = declaration.find('*', p)) != string::npos) {
      arity++;
      varstring += ",x" + arity;
      p++;
    }
  }

  string query = "QUERY do-simplify [" + f + " " + g + "] and "
    "equivalence " + f + "(" + varstring + ") -><- " + g + "(" +
    varstring + ") " + equiv_info->constraint;

  for (i = lines.size()-1; i >= 0 &&
       lines[i].substr(0,5) != "QUERY"; i--);
  if (i < 0) lines.push_back(query);
  else {
    lines[i] = query;
    lines.resize(i+1);
  }
}

// avoids duplicates in the signature; gives an error message and
// returns an error message if there are duplicates that cannot be
// merged
string avoid_signature_duplicates(string &firstdec) {
  bool sig = false;
  string errdec = "", retdec = "";
  int j = 0;

  for (int i = 0; i < lines.size(); i++, j++) {
    if (lines[i] == "SIGNATURE") sig = true;
    else if (lines[i] == "RULES") sig = false;
    if (!sig) { lines[j] = lines[i]; continue; }
    size_t k = lines[i].find(':');
    if (k == string::npos) { lines[j] = lines[i]; continue; }

    string symbol = trim(lines[i].substr(0,k));
    string declaration = trim(lines[i].substr(k+1));

    // fun1 : dec or fun2 : dec -- check for consistency of dec
    if (symbol == equiv_info->fun1 || symbol == equiv_info->fun2) {
      if (firstdec == "") firstdec = declaration;
      else if (firstdec != declaration)
        return "These functions have different type declarations.  If "
               "this is not the case in the C-file, then most likely "
               "they rely on different global variables.";
    }
    // errors (have already been renamed)
    if (symbol == "error") {
      if (errdec == "") errdec = declaration;
      else if (errdec != declaration)
        return "These functions somehow end up having different type "
               "declarations for the error types!";
      else { j--; continue; }
    }
    // returns (have already been renamed)
    if (symbol == "return") {
      if (retdec == "") retdec = declaration;
      else if (retdec != declaration)
        return "These functions are not equivalent, because they "
          "affect different global variables and changeable arguments.";
      else { j--; continue; }
    }

    lines[j] = lines[i];
  }

  lines.resize(j);
  return "";
}

// main function for the equivalence case
string handle_equivalence() {
  string query = "";
  int i;

  // split off and parse the query
  for (i = 0; i < lines.size(); i++) {
    lines[i] = trim(lines[i]);
    if (lines[i] != "") break;
  }
  query = read_query(i >= lines.size() ? "" : lines[i]);
  if (query == "") return "Error reading input: missing query.";
  if (!parse_query(query)) return "Illegal query: " + query;
  if (equiv_info == NULL) return "Unexpected query: " + query;

  // write the rest to file together and call c2lctrs
  write_merged_file("xxxa.c", i + 1);
  system("./c2lctrs xxxa.c > xxxb.ctrs");
  lines.clear();
  load_file("xxxb.ctrs", false);

  // adapt the LCTRS file for equivalence checking
  replace_main_name(equiv_info->fun1);
  replace_main_name(equiv_info->fun2);
  string maindec = "";
  string tmp = avoid_signature_duplicates(maindec);
  if (tmp != "") return tmp;
  fix_equivalence_query(equiv_info->fun1, equiv_info->fun2, maindec);

  // write the resulting query to file
  write_merged_file("xxxc.ctrs", 0);
  system("./ctrl xxxc.ctrs");
  return "";
}


/*****************************************************************************/
/*                            MAIN FUNCTIONALITY                             */
/*****************************************************************************/

string run(vector<string> args) {
  if (args.size() != 1) return "SYNTAX: ./ctrl <filename>";

  // try whether we have a reference implementation or a specification
  size_t start = args[0].find_last_of("/\\");
  if (start == string::npos) start = 0;
  else start++;
  size_t p = args[0].find_last_of('_');
  if (p != string::npos) {
    string sf = SPECIFICATIONS_PATH + args[0].substr(start, p-start) + ".spec";
    load_file(sf, false);
    if (lines.size() > 0) {
      read_specification_file();
      lines.clear();
      load_file(args[0], true);
      return handle_specification();
    }
    string rf = REFERENCES_PATH + args[0].substr(start, p-start) + ".c";
    load_file(rf, false);
    load_file(args[0], true);
    return handle_equivalence();
  }
}

// standard main function
int main(int argc, char **argv) {
  vector<string> args;
  for (int i = 1; i < argc; i++) args.push_back(argv[i]);
  string err = run(args);
  if (err != "") cout << err << endl;
  return 0;
}

