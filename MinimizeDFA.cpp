/*  C++ code for Minimizing a DFA given as input from file.  
    AUTHOR = KAPEEL SURYAVANSHI             ENROLLMENT NUMBER = BT16CSE084 */
    
/*Please Note : The input in the file should be space separated.(example : NT = A B F) First Line of file (starting with NT) 
is set of non terminal states, second line of file (starting with F) is set of final or terminal states, third line is set of input symbols
and its following lines are part of transition table.*/

#include<bits/stdc++.h>
#define breakline() cout<<"-------------------------------------------------------------------------\n"
using namespace std;

void print(map<string,vector<string> > &table,vector<string> &nonterm_states, vector<string> &final_states,vector<string> &input_symbols)
{
    int i,j;
    breakline();
    cout<<"Non Terminal States : \n";
    for(i=0 ; i<nonterm_states.size() ; i++)
    {
        cout<<nonterm_states[i]<<"  ";
    }
    cout<<endl;
    cout<<"Final States : \n";
    for(i=0 ; i<final_states.size() ; i++)
    {
        cout<<final_states[i]<<"  ";
    }
    cout<<endl;
    cout<<"Input Symbols ("<<input_symbols[0]<<") & Transition Table :\n";
    for(i=0 ; i<input_symbols.size() ; i++)
    {
        cout<<input_symbols[i]<<"\t";
    }
    cout<<endl;
    //cout<<"Transition Table :\n";
    for(map<string, vector<string> >::iterator it = table.begin() ; it!=table.end() ; it++)
    {
        cout<<it->first<<"\t";
        for(j=0 ; j<it->second.size() ; j++)
        {
            cout<<it->second[j]<<"\t";
        }
        cout<<endl;
    }
    breakline();
}

void remove_unreachable_states(map<string,vector<string> > &table,vector<string> &nonterm_states, vector<string> &final_states)
{
    map<string,bool> reached;
    int i,j;
    for(i=0 ; i<nonterm_states.size() ; i++)
    {
        reached.insert(make_pair<string,bool>(nonterm_states[i],0));
    }
    for(i=0 ; i<final_states.size() ; i++)
    {
        reached.insert(make_pair<string,bool>(final_states[i],0));
    }
    
    queue<string> q;
    string t;
    reached[nonterm_states[0]] = 1;
    for(i=0 ; i<table[nonterm_states[0]].size() ; i++)
    {
        q.push(table[nonterm_states[0]][i]);
    }
    
    //using BFS to keep track of visited states
    while(!q.empty())
    {
        t = q.front();
        if(!reached[t])
        {
            reached[t] = 1;
            for(i=0 ; i<table[t].size() ; i++)
            {
                q.push(table[t][i]);
            }
        }
        q.pop();
    }
    
    for(map<string,bool>::iterator r=reached.begin() ; r!=reached.end() ; r++)
    {
        if(!r->second)
        {
            string t = (string)r->first;
            
            //cout<<"Removing from table\n";
            table.erase(t);
            
            vector<string>::iterator it1,it2;
            it1 = find(nonterm_states.begin(),nonterm_states.end(),t);
            it2 = find(final_states.begin(),final_states.end(),t);
            if(it1 != nonterm_states.end())
            {
                //cout<<"Removing from non terminal states\n";
                nonterm_states.erase(it1,it1+1);
            }
            else if(it2 != final_states.end())
            {
                //cout<<"Removing from final states\n";
                final_states.erase(it2,it2+1);
            }
            
        }
    }
    //print(table,nonterm_states,final_states);
}

void update_set(vector<vector<string> > &set,map<string,int> &m,int max_num_set,int &curr_num_set)
{
    int i,j;
    set.resize(max_num_set);
    for(i=0 ; i<curr_num_set ; i++)
    {
        for(j=0 ; j<set[i].size() ; j++)
        {
            
            if(m[ set[i][j] ] != i)
            {
                set[ m[set[i][j]] ].push_back(set[i][j]); 
                set[i].erase(set[i].begin()+j,set[i].begin()+j+1);
                j--;
            }    
        }
    }
    curr_num_set = max_num_set;
}

void update_table_n_states(vector<string> &comb_set, map<string,int> &m, map<string,vector<string> > &table, vector<string> &nonterm_states, vector<string> &final_states)
{   
    int i,j;
    
    map<string, vector<string> > newtable;
    for(map<string, vector<string> >::iterator it = table.begin() ; it!=table.end() ; it++)
    {
        newtable[ comb_set[ m[it->first] ] ];
        for(j=0 ; j<it->second.size() ; j++)
        {
            if(newtable[ comb_set[ m[it->first] ] ].size() < it->second.size())
                newtable[ comb_set[ m[it->first] ] ].push_back(comb_set[ m[it->second[j]] ]);
        }
    }
    table.clear();
    //update old transition table to new one
    table = newtable;
    
    //update non terminal states
    for(i=0 ; i<nonterm_states.size() ; i++)
    {
        if( (comb_set[ m[nonterm_states[i]] ].size()) > 0)
        {
            string t = comb_set[ m[nonterm_states[i]] ];
            comb_set[ m[nonterm_states[i]] ].clear();
            nonterm_states[i] = t;
        }
        else
        {
            nonterm_states.erase(nonterm_states.begin()+i,nonterm_states.begin()+i+1);
            i--;
        }
    }
    
    //update final states (terminal states)
    for(i=0 ; i<final_states.size() ; i++)
    {
        if( (comb_set[ m[final_states[i]] ].size()) > 1)
        {
            string t = comb_set[ m[final_states[i]] ];
            comb_set[ m[final_states[i]] ].clear();
            final_states[i] = t;
        }
        else
        {
            final_states.erase(final_states.begin()+i,final_states.begin()+i+1);
            i--;
        }
    }
    //print(table,nonterm_states,final_states);
}

void Minimize_DFA(map<string,vector<string> > &table, vector<string> &nonterm_states, vector<string> &final_states,int inp_sym)
{
    remove_unreachable_states(table,nonterm_states,final_states);
    
    int i,j;
    map<string,int> m;
    vector<vector<string> > set;
    vector<string> t,curr_set;
    int s,curr_num_set,max_num_set,eq_set;
    bool change = 1,flag=0;
    
    //make initial sets
    for(i=0 ; i<nonterm_states.size() ; i++)
    {
        m[nonterm_states[i]] = 0;
        t.push_back(nonterm_states[i]);
    } 
    set.push_back(t);
    t.clear();   
    for(i=0 ; i<final_states.size() ; i++)
    {
        m[final_states[i]] = 1;
        t.push_back(final_states[i]);
    }
    set.push_back(t);
    t.clear();
    
    //start minimizing 
    curr_num_set = 2;           //number of sets in vector
    max_num_set = 2;            //number of sets initially in vector + any new set to be formed
    while(change)
    {
        
        for(s=0 ; s<inp_sym ; s++)
        {
            change = 0;
            for(i=0 ; i<curr_num_set ; i++)
            {
                flag = 0;
                curr_set = set[i];
                string p =  table[curr_set[0]][s];
                
                eq_set = m[ table[curr_set[0]][s] ];
                for(j=1 ; j<curr_set.size() ; j++)
                {
                    if( m[ table[curr_set[j]][s] ] != eq_set )
                    {
                        change = 1;
                        flag = 1;
                        m[ curr_set[j] ] = max_num_set;
                        p = curr_set[j];
                    }
                }
                if(flag)
                {
                    max_num_set++;
                    flag = 0;
                }
            }
            if(change)
            {
                update_set(set,m,max_num_set,curr_num_set);
            }
                
        }
    }
    
    //combine the sets into 1 strings
    vector<string> comb_set;
    string temp;
    for(i=0 ; i<set.size() ; i++)
    {
        temp.clear();
        for(j=0 ; j<set[i].size() ; j++)
        {
            temp += set[i][j];
        }
        comb_set.push_back(temp);
    }
    set.clear();
    
    //update the parameters of DFA
    update_table_n_states(comb_set,m,table,nonterm_states,final_states);
}

int main()
{
    vector<string> final_states;
    map<string,vector<string> >  table;
    vector<string> nonterm_states;
    vector<string> input_symbols;
    
    string line,ch,t;
    int i,j;
    bool  flag = 0;
    ifstream fin;
    fin.open("dfa_input");
    if(!fin)
    {
        cerr<<"Error in Opening File\n";
        exit(1);
    }      
    while(getline(fin,line))
    {
        istringstream ss(line);
        ss>>ch;
        if(ch.compare("NT")==0)
        {
            ss>>ch;
            //cout<<"Reading Non Terminal States\n";
            while(ss>>ch)
            {
                nonterm_states.push_back(ch);
            }
        }
        else if(ch.compare("F")==0 && !flag)
        {
            ss>>ch;
            //cout<<"Reading Final States(Terminal States)\n";
            while(ss>>ch)
            {
                final_states.push_back(ch);
            }
        }
        else if(ch.compare("Σ")==0)
        {
            input_symbols.push_back(ch);
            while(ss>>ch)
            {
                input_symbols.push_back(ch);
            }
            flag = 1;
        }
        else
        {
            t = ch;
            //vector<string> row;
            while(ss>>ch)
            {
                table[t].push_back(ch);
            }
            //tabl.push_back(row);
        }
    }
    
    cout<<"DFA given as input :\n";
    print(table,nonterm_states,final_states,input_symbols);
    
    Minimize_DFA(table,nonterm_states,final_states,input_symbols.size()-1);
    
    cout<<"DFA After Minimizing :\n";
    print(table,nonterm_states,final_states,input_symbols);

    return 0;
}
