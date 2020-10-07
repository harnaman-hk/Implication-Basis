#include <bits/stdc++.h>
using namespace std;

void skipLines(int n)
{
    string line;

    for(int i = 0; i < n; i++)
        getline(cin, line);
}

int main()
{
    string line;
    skipLines(2);
    int nObj, nAttr;
    cin >> nObj >> nAttr;
    skipLines(nObj + nAttr + 2);

    for(int i = 0; i < nObj; i++)
    {
        getline(cin, line);

        for(int j = 0; j < line.length(); j++)
        {
            if(line[j] == 'X')
                cout << j + 1 <<" ";
        }

        cout <<"\n";
    }

    return 0;
}