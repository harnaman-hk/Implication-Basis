#include <bits/stdc++.h>
using namespace std;

int main(int argc, char* argv[])
{
    ifstream ifile(argv[1]);
    string line;
    map <string, int> attrMap;
    map <int, string> attrInvMap;
    vector<vector<int> > objects;

    while(getline(ifile, line))
    {
        vector<int> cObj;
        istringstream iss(line);
        string word;

        while(iss >> word)
        {
            if(attrMap.find(word) == attrMap.end())
            {
                attrMap[word] = attrMap.size() + 1;
                attrInvMap[attrMap[word]] = word;
            }

            cObj.push_back(attrMap[word]);
        }

        objects.push_back(cObj);
    }

    ifile.close();
    cout <<"B\n\n";
    cout << objects.size() <<"\n";
    cout << attrMap.size() <<"\n\n";

    for(int i = 1; i <= objects.size(); i++)
        cout << i <<"\n";

    for(auto attr:attrInvMap)
        cout << attr.second <<"\n";

    for(int i = 0; i < objects.size(); i++)
    {   
        string cObj;

        for(int j = 0; j < attrInvMap.size(); j++)
            cObj += '.';

        for(int j = 0; j < objects[i].size(); j++)
            cObj[objects[i][j] - 1] = 'X';    

        cout << cObj <<"\n";    
    }   

    return 0;     
}