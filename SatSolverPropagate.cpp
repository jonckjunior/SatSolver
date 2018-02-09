#include <bits/stdc++.h>

using namespace std;


struct stateClausula{
    int numTrue, numFalse, numNoValue;
    stateClausula(int _numTrue, int _numFalse, int _numNoValue){
        numTrue = _numTrue; numFalse = _numFalse; numNoValue = _numNoValue;
    }
};

typedef pair<int,int> ii;
typedef vector<ii> vii;
typedef vector<int> vi;
typedef vector<vi> vvi;
typedef vector<stateClausula> vs;
const int NOVALUE = -1;


int num_var, num_clausula;
vvi clausula;
vi model;
vs clausula_count;
vvi lit_to_clausula;
vii trail;

int indexOffSet(int p){
    if(p > 0) return p;
    else      return abs(p) + num_var;
}

bool isSat(){
    for(int i = 0; i < (int)clausula.size(); i++){
        bool found = false;
        for(int j = 0; j < (int) clausula[i].size(); j++){
            int var = clausula[i][j];
            if(var > 0 && model[var] == 1) found = true;
            if(var < 0 && model[abs(var)] == 0) found = true;
        }
        if(found == false)
            return false;
    }
    return true;
}

int findNotAssigned(int idxClausula){
    for(int var : clausula[idxClausula]){
        //printf("model[%d] = %d\n", var, model[abs(var)]);
        if(model[abs(var)] == NOVALUE)
            return var;
    }
    return 0;
    printf("---[#] FINDNOTASSIGNED DIDNT FIND NOT ASSIGNED\n");
    exit(0);
}

int decide(){
    for(int i = 0; i < (int)clausula_count.size(); i++){
        if(clausula_count[i].numTrue == 0 && clausula_count[i].numNoValue == 2)
            return findNotAssigned(i);
    }
    for(int i = 1; i < (int)model.size(); i++)
        if(model[i] == NOVALUE)
            return i;
    printf("---[#] ERROR DECIDE CANT PICK VARIABLE\n");
    exit(0);
}

int clausulas_aprendidas = 0;
int num_propagation = 0;

bool propagate(int p, int nivel){
    num_propagation++;
    // printf("propagating %d\n",p);
    int notp = -p;
    trail.push_back(ii(p, nivel));
    if(p > 0) model[p] = 1;
    else      model[notp] = 0;  
    vi& clausula_notp = lit_to_clausula[indexOffSet(notp)];
    vi& clausula_p    = lit_to_clausula[indexOffSet(p)];
    vi clausulas_unitarias;
    for(int c : clausula_p){
        clausula_count[c].numTrue++;
        clausula_count[c].numNoValue--;
    }
    bool conflito_encontrado = false;
    for(int c : clausula_notp){
        clausula_count[c].numFalse++;
        clausula_count[c].numNoValue--;
        if(clausula_count[c].numNoValue == 1 && clausula_count[c].numTrue == 0){
            //printf("propagating %d found unitary %d\n", p, c);
            clausulas_unitarias.push_back(c);
        }
        if(clausula_count[c].numNoValue == 0 && clausula_count[c].numTrue == 0){
            conflito_encontrado = true;
        }
    }
    
    if(conflito_encontrado){
        clausulas_aprendidas++;
        return false;
    }
    
    for(int unitaria : clausulas_unitarias){
        //printf("clausula unitaria %d com %d falsos, vindo de %d\n", unitaria, clausula_count[unitaria].numFalse, p);
        int varNotAssigned = findNotAssigned(unitaria);
        if(varNotAssigned == 0) continue;
        if(!propagate(varNotAssigned, nivel)){
            clausulas_aprendidas++;
            return false;
        }
    }
    return true;
}

void backtrack(int nivel, bool learning){
    int firstPropagated = 0;

    while(!trail.empty()){
        ii topo = trail.back();
        if(topo.second < nivel) break;
        firstPropagated = topo.first;
        int notp = -topo.first;
        model[abs(notp)] = NOVALUE;
        vi& clausula_notp = lit_to_clausula[indexOffSet(notp)];
        vi& clausula_p    = lit_to_clausula[indexOffSet(topo.first)];
        for(int c : clausula_notp){
            clausula_count[c].numFalse--;
            clausula_count[c].numNoValue++;
        }
        for(int c : clausula_p){
            clausula_count[c].numTrue--;
            clausula_count[c].numNoValue++;
        }
        trail.pop_back();
    }
}
int contador = 0;
bool solve(int nivel){
    //printf("solving\n");
    if(trail.size() == num_var){
        return isSat();
    }
    else{
        //printf("TRAIL SIZE IS = %d\n", (int)trail.size());
        contador++;
        if(contador%1000000 == 0) printf("trail size = %d e nivel = %d\n", (int)trail.size(), nivel), contador = 0;
        int choice = decide();
        bool prop = propagate(choice, nivel);
        
        if(prop){
            if(solve(nivel+1))
                return true;
            else
                backtrack(nivel, false);
        }
        else{
            backtrack(nivel, true);
        }

        prop = propagate(-choice, nivel);

        if(prop){
            if(solve(nivel+1))
                return true;
            else
                backtrack(nivel, false);
        }
        else{
            backtrack(nivel, true);
        }

        return false;
    }
}

int main(){
    
    cin >> num_var >> num_clausula;
    
    clausula.assign(num_clausula, vi());
    model.assign(num_var+1, NOVALUE);
    clausula_count.assign(num_clausula, stateClausula(0,0,3));
    lit_to_clausula.assign(num_var*2+5, vi());

    for(int i = 0; i < num_clausula; i++){
        for(int j = 0; j < 3; j++){
            int x; cin >> x;
            clausula[i].push_back(x);
            lit_to_clausula[indexOffSet(x)].push_back(i);
        }
        int token; cin >> token;
    }
    
    bool found = solve(0);
    
    if(found){
        cout << "SAT" << endl;
        for(int i = 0; i < (int)model.size(); i++){
            cout << model[i] << " ";
        }
        cout << endl;
    }
    else{
        cout << "UNSAT" << endl;
    }
    printf("clausulas que seriam aprendidas = %d\n", clausulas_aprendidas);
    printf("num propagation = %d\n", num_propagation);
    return 0;
}
