#include <bits/stdc++.h>
using namespace std;
const int TRUE = 1, FALSE = 0, NOVALUE = -1;

class SatSolver{
    int numVar, numClausula;
    vector<int> modelo, numTrue, numFalse, numNoValue;
    vector< pair<int,int> > trail;
    vector< vector<int> > vetor_clausula;
    map<int, vector<int> > literal_to_clausula;
    
    public:
        SatSolver(int _numVar){
            numVar = _numVar;
            modelo.assign(numVar+1, NOVALUE);
        }
        
        bool solve(int nivel){
            if((int)trail.size() == numVar)
                return true;
            else{
                int variavel_designada = decide();
                if(variavel_designada == 0){
                    printf("PEGOU ERRADO\n");
                    exit(0);
                }
                int notVariavel_designada = -variavel_designada;
                bool prop = propagate(variavel_designada, nivel);
                
                if(prop && solve(nivel+1))
                    return true;
                else
                    backtrack(nivel);
                
                prop = propagate(notVariavel_designada, nivel);
                
                if(prop && solve(nivel+1))
                    return true;
                else
                    backtrack(nivel);
            }
            return false;
        }
        
        bool isSat(){
            for(vector<int>& clausula : vetor_clausula){
                bool satisfeita = false;
                for(int var : clausula){
                    if(var > 0 && modelo[var] == TRUE) satisfeita = true;
                    if(var < 0 && modelo[-var] == FALSE) satisfeita = true;
                }
                if(satisfeita == false)
                    return false;
            }
            return true;
        }
        
        int findNotAssigned(int idxClausula){
            for(int variavel : vetor_clausula[idxClausula])
                if(modelo[abs(variavel)] == NOVALUE)
                    return variavel;
            return 0;
        }
        
        int decide(){
            for(int i = 0; i < numClausula; i++)
                if(numTrue[i] == 0 && numNoValue[i] == 2)
                    return findNotAssigned(i);
            for(int i = 1; i < modelo.size(); i++)
                if(modelo[i] == NOVALUE)
                    return i;
            printf("---[#] ERROR DECIDE CANT PICK VARIABLE\n");
            exit(-1);
        }
        
        bool propagate(int p, int nivel){
            int notp = -p;
            trail.push_back(pair<int,int>(p, nivel));
            if(p > 0) modelo[p] = TRUE;
            else      modelo[notp] = FALSE;
            
            vector<int>& clausula_notp = literal_to_clausula[notp];
            vector<int>& clausula_p    = literal_to_clausula[p];
            
            for(int clausula : clausula_p){
                numTrue[clausula]++;
                numNoValue[clausula]--;
            }
            
            bool conflito_encontrado = false;
            vector<int> clausulas_unitarias;
            
            for(int clausula : clausula_notp){
                numFalse[clausula]++;
                numNoValue[clausula]--;
                if(numNoValue[clausula] == 1 && numTrue[clausula] == 0)
                    clausulas_unitarias.push_back(clausula);
                if(numNoValue[clausula] == 0 && numTrue[clausula] == 0)
                    conflito_encontrado = true;
            }
            
            if(conflito_encontrado == true)
                return false;
            
            for(int unitaria : clausulas_unitarias){
                int variavelNotAssigned = findNotAssigned(unitaria);
                if(variavelNotAssigned == 0) continue;
                if(propagate(variavelNotAssigned, nivel) == false)
                    return false;
            }
            return true;
        }
        
        void backtrack(int nivel_backtrack){
            while(!trail.empty()){
                int p = trail.back().first, nivel_p = trail.back().second;
                int notp = -p;
                
                if(nivel_p < nivel_backtrack)
                    break;
                
                modelo[abs(p)] = NOVALUE;
                
                vector<int>& clausula_notp = literal_to_clausula[notp];
                vector<int>& clausula_p    = literal_to_clausula[p];
                
                for(int clausula : clausula_notp){
                    numFalse[clausula]--;
                    numNoValue[clausula]++;
                }
                
                for(int clausula : clausula_p){
                    numTrue[clausula]--;
                    numNoValue[clausula]++;
                }
                trail.pop_back();
            }
        }
        
        void addClausula(vector<int>& clausula){
            int idxClausula = (int)vetor_clausula.size();
            for(int variavel : clausula)
                literal_to_clausula[variavel].push_back(idxClausula);
            numTrue.push_back(0);
            numFalse.push_back(0);
            numNoValue.push_back(clausula.size());
            vetor_clausula.push_back(clausula);
            numClausula = vetor_clausula.size();
        }
        
        void printClausula(){
            for(vector<int>& clausula : vetor_clausula){
                for(int var : clausula)
                    cout << var << " ";
                cout << endl;
            }
        }
        
        void printSolution(){
            if(solve(0)){
                cout << "SAT" << endl;
                for(int i = 1; i < modelo.size(); i++)
                    cout << modelo[i] << " ";
                cout << endl;
            }
            else
                cout << "UNSAT" << endl;
        }
};


int main(){
    int numVar, numClausula;
    cin >> numVar >> numClausula;
    
    SatSolver solver(numVar);
    
    for(int i = 0; i < numClausula; i++){
        vector<int> clausula;
        for(int j = 0; j < 3; j++){
            int var; cin >> var;
            clausula.push_back(var);
        }
        solver.addClausula(clausula);
        int token; cin >> token;
    }
    //solver.printClausula();
    solver.printSolution();
    return 0;
}
