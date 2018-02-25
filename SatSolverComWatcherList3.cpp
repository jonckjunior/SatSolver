#include <bits/stdc++.h>
using namespace std;
const int TRUE = 1, FALSE = 0, NOVALUE = -1;
int contadorzera = 0;
class SatSolver{
    int numVar, numClausula;
    vector<int> modelo;
    pair<int,int> clausulas_implicadas;
    vector< pair<int,int> > trail;
    vector< vector<int> > vetor_clausula;
    vector< pair<int,int> > clausula_to_watcher;
    vector< list<int> > watcher_to_clausula;
    set< vector<int> > usadas;

    public:
        SatSolver(int _numVar){
            numVar = _numVar;
            modelo.assign(numVar+1, NOVALUE);
            watcher_to_clausula.assign(2*numVar+5, list<int>());
        }
        
        bool solve(int nivel){
            if((int)trail.size() == numVar)
                return true;
            else{
                int variavel_designada = decide();
                if(variavel_designada == 0){
                    printf("ERRO EM SOLVE, FUNCAO DECIDE RETORNOU 0\n");
                    exit(-1);
                }
                int notVariavel_designada = -variavel_designada;

                bool prop = propagate(variavel_designada, nivel, -1);
                if(prop && solve(nivel+1))
                    return true;
                else
                    backtrack(nivel);
                
                prop = propagate(notVariavel_designada, nivel, -1);
                
                if(prop && solve(nivel+1))
                    return true;
                else
                    backtrack(nivel);
            }
            return false;
        }
        
        int indexOffSet(int p){
            if(p > 0) return p;
            else      return abs(p) + numVar;
        }

        int findNotAssigned(int idxClausula){
            for(int variavel : vetor_clausula[idxClausula])
                if(modelo[abs(variavel)] == NOVALUE)
                    return variavel;
            return 0;
        }

        int findNewWatcher(int idxClausula, int otherWatcher){
            for(int variavel : vetor_clausula[idxClausula]){
                // contadorzera++;
                bool aux = (variavel < 0 && modelo[-variavel] == FALSE) || (variavel > 0 && modelo[variavel] == TRUE);
                if(variavel != otherWatcher && (aux || modelo[abs(variavel)] == NOVALUE))
                    return variavel;
            }
            return 0;
        }

        bool isSat(){
            for(vector<int>& clausula : vetor_clausula){
                bool found = false;
                for(int variavel : clausula)
                    if(variavel < 0 && modelo[-variavel] == FALSE || variavel > 0 && modelo[variavel] == TRUE)
                        found = true;
                if(!found) return false;
            }
            return true;
        }
        
        int decide(){
            for(int i = 1; i < modelo.size(); i++)
                if(modelo[i] == NOVALUE)
                    return i;
            printf("---[#] ERROR DECIDE CANT PICK VARIABLE\n");
            exit(-1);
        }
        
        bool propagate(int p, int nivel, int clausula_propagada){
            // printf("propagando %d %d\n", p, nivel);
            int notp = -p;
            trail.push_back(pair<int,int>(p, nivel));
            if(p > 0) modelo[p] = TRUE;
            else      modelo[notp] = FALSE;

            vector<int> clausulas_unitarias;
            
            for(auto it = watcher_to_clausula[ indexOffSet(notp) ].begin(); it != watcher_to_clausula[ indexOffSet(notp) ].end(); it++){
                // contadorzera++;
                int clausula = *it;
                int watcher1 = clausula_to_watcher[clausula].first;
                int watcher2 = clausula_to_watcher[clausula].second;
                if(watcher1 != notp) swap(watcher1, watcher2);

                int newWatcher = findNewWatcher(clausula, watcher2);
                bool stateWatcher2 = (watcher2 < 0 && modelo[-watcher2] == FALSE) || (watcher2 > 0 && modelo[watcher2] == TRUE);

                if(newWatcher != 0 && (stateWatcher2 || modelo[abs(watcher2)] == NOVALUE)){
                    watcher_to_clausula[ indexOffSet(newWatcher) ].push_back(clausula);
                    clausula_to_watcher[clausula] = pair<int,int>(newWatcher, watcher2);

                    it = watcher_to_clausula[ indexOffSet(watcher1) ].erase(it);
                    it--;
                }
                else if(newWatcher == 0 && modelo[abs(watcher2)] == NOVALUE)
                    clausulas_unitarias.push_back(clausula);
                else if(newWatcher == 0 && modelo[abs(watcher2)] != NOVALUE && !stateWatcher2){
                    clausulas_implicadas = pair<int,int>(clausula_propagada, clausula);
                    return false;
                }
            }

            for(int unitaria : clausulas_unitarias){
                int variavelNotAssigned = findNotAssigned(unitaria);
                if(variavelNotAssigned == 0) continue;
                if(propagate(variavelNotAssigned, nivel, unitaria) == false)
                    return false;
            }
            return true;
        }
        
        void backtrack(int nivel_backtrack){
            while(!trail.empty()){
                int p = trail.back().first, nivel_p = trail.back().second;
                
                if(nivel_p < nivel_backtrack)
                    break;
                
                modelo[abs(p)] = NOVALUE;
                
                trail.pop_back();
            }
        }
        
        void addClausula(vector<int>& clausula){
            int idxClausula = (int)vetor_clausula.size();
            int watcher1 = clausula[0], watcher2 = clausula[1];

            watcher_to_clausula[ indexOffSet(watcher1) ].push_back(idxClausula);
            watcher_to_clausula[ indexOffSet(watcher2) ].push_back(idxClausula);
            clausula_to_watcher.push_back(pair<int,int>(watcher1, watcher2));

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
                cout << isSat() << endl;
                cout << "SAT" << endl;
                for(int i = 1; i < modelo.size(); i++)
                    cout << modelo[i] << " ";
                cout << endl;
            }
            else
                cout << "UNSAT" << endl;
            cout << contadorzera << endl;
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
    // solver.printClausula();
    solver.printSolution();
    return 0;
}
