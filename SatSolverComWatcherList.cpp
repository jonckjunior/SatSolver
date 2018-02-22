#include <bits/stdc++.h>
using namespace std;
const int TRUE = 1, FALSE = 0, NOVALUE = -1;

class SatSolver{
    int numVar, numClausula;
    vector<int> modelo;
    vector< pair<int,int> > trail;
    vector< vector<int> > vetor_clausula;
    map<int, vector<int> > literal_to_clausula;
    map<int, pair<int,int> > clausula_to_watcher;
    map<int, set<int> > watcher_to_clausula;
    
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
        
        int findNotAssigned(int idxClausula){
            for(int variavel : vetor_clausula[idxClausula])
                if(modelo[abs(variavel)] == NOVALUE)
                    return variavel;
            return 0;
        }

        int findNewWatcher(int idxClausula, int otherWatcher){
            for(int variavel : vetor_clausula[idxClausula]){
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
        
        bool propagate(int p, int nivel){
            // printf("propagando %d %d\n", p, nivel);
            int notp = -p;
            trail.push_back(pair<int,int>(p, nivel));
            if(p > 0) modelo[p] = TRUE;
            else      modelo[notp] = FALSE;

            vector<int> clausulas_unitarias;
            
            set<int> clausula_notp = watcher_to_clausula[notp];
            for(int clausula : clausula_notp){
                int watcher1 = clausula_to_watcher[clausula].first;
                int watcher2 = clausula_to_watcher[clausula].second;
                if(watcher1 != notp) swap(watcher1, watcher2);
                // printf("w1 = %d, w2 = %d\n", watcher1, watcher2);
                int newWatcher = findNewWatcher(clausula, watcher2);
                // printf("newWatcher de clausula %d = %d\n", clausula, newWatcher);
                bool stateWatcher2 = (watcher2 < 0 && modelo[-watcher2] == FALSE) || (watcher2 > 0 && modelo[watcher2] == TRUE);
                // printf("stateWatcher2 = %d\n", stateWatcher2);
                if(newWatcher != 0 && (stateWatcher2 || modelo[abs(watcher2)] == NOVALUE)){
                    watcher_to_clausula[newWatcher].insert(clausula);
                    clausula_to_watcher[clausula] = pair<int,int>(newWatcher, watcher2);
                    watcher_to_clausula[watcher1].erase(clausula);
                }
                else if(newWatcher == 0 && modelo[abs(watcher2)] == NOVALUE){
                    // printf("achou unitaria %d\n", clausula);
                    clausulas_unitarias.push_back(clausula);
                }
                else if(newWatcher == 0 && modelo[abs(watcher2)] != NOVALUE && !stateWatcher2)
                    return false;
            }

            for(int unitaria : clausulas_unitarias){
                int variavelNotAssigned = findNotAssigned(unitaria);
                if(variavelNotAssigned == 0) continue;
                if(propagate(variavelNotAssigned, nivel) == false)
                    return false;
            }
            return true;
        }
        
        void backtrack(int nivel_backtrack){
            // printf("deu treta\n");
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
            for(int variavel : clausula)
                literal_to_clausula[variavel].push_back(idxClausula);
            int watcher1 = clausula[0], watcher2 = clausula[1];

            watcher_to_clausula[watcher1].insert(idxClausula);
            watcher_to_clausula[watcher2].insert(idxClausula);
            clausula_to_watcher[idxClausula] = pair<int,int>(watcher1, watcher2);

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
