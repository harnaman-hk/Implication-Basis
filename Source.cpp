#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>
#include <thread>
#include <set>
#include <time.h>
#include <stdlib.h>
#include <chrono>
#include <cmath>
#include <random>
#include <unordered_set>
#include <boost/dynamic_bitset.hpp>

using namespace std;

typedef struct s 
{
	vector<int> lhs;
	vector<int> rhs;
}implication;

vector<vector<int>> objInp;			//For storing which attributes are associated with which objects
vector<vector<int>> attrInp;		//For storing which objects are associated with which attributes
vector<boost::dynamic_bitset<unsigned long> > objInpBS;
double totalTime = 0;	
double totalExecTime2 = 0;		//Stores total time spent generating counter examples
double totalClosureTime = 0;
double intersectionTime = 0;
double thisIterMaxImplicationClosureTime = 0;
double thisIterMaxContextClosureTime = 0;
double updownTime = 0;
int numThreads = 1;
long long totCounterExamples = 0;
bool globalFlag;					//For terminating other threads in case one thread found a counter-example
vector<int> counterExample;
int gCounter = 0;					//For counting how many times the equivalence oracle has been used
int totTries = 0;	
long long totClosureComputations = 0;
long long totUpDownComputes = 0;				//Stores how many random attribute sets needed to be tested before finding a counter-example. For debugging purposes. 

vector<vector<int>> potentialCounterExamples;
double epsilon, del; 
bool epsilonStrong = false, frequentCounterExamples = false;
int maxTries;						//Updated by getLoopCount() based on the value of gCounter, epsilon and delta.

std::random_device rd;
std::discrete_distribution<int> discreteDistribution;
std::default_random_engine re(rd());

vector<long double> attrSetWeight;

void initializeRandSetGen()
{
	attrSetWeight.resize(objInp.size());

	for(int i = 0; i < objInp.size(); i++)
	{
		attrSetWeight[i] = (long double)pow((long double) 2, (long double) objInp[i].size());
	}

	discreteDistribution = std::discrete_distribution<int> (attrSetWeight.begin(), attrSetWeight.end());
}

void getLoopCount()
{
	double loopCount = log(del / ((double)(gCounter * (gCounter + 1))));
	loopCount = loopCount / log(1 - epsilon);
	maxTries = (int)ceil(loopCount);
}

void printVector(vector<int> &A) 
{
	for (auto x : A) 
	{
		//cout << x << " ";
	}

	//cout << "\n";
}

vector<int> intersection(vector<int> &A, vector<int> &B) 
{
	unordered_set <int> Bset(B.begin(), B.end());
	vector<int> ans;

	for (int i = 0; i < A.size(); i++) 
	{
		if (Bset.find(A[i]) != Bset.end()) 
			ans.push_back(A[i]);
	}
	
	return ans;
}

vector<int> vunion(vector<int> &A, vector<int> &B) 
{
	vector<int> ans;
	set<int> tmp;
	for (auto x : A) tmp.insert(x);
	for (auto x : B) tmp.insert(x);
	for (auto x : tmp) ans.push_back(x);
	return ans;
}

bool subvector(vector<int> &A, vector<int> &B) 
{
	sort(B.begin(), B.end());
	for (int i = 0; i < A.size(); i++) {
		if (!binary_search(B.begin(), B.end(), A[i])) return false;
	}
	return true;
}

bool verifyImplication(implication &A) 
{
	for (auto x : objInp) {
		if (subvector(A.lhs, x) && !subvector(A.rhs, x)) {
			return false;
		}
	}
	return true;
}

bool isAaSubsetOfB(vector<int> &A, vector<int> &B)
{
	unordered_set<int> Bset(B.begin(), B.end());
	int Asz = A.size();

	for(int i = 0; i < Asz; i++)
		if(Bset.find(A[i]) == Bset.end())
			return false;

	return true;		
}

vector<int> attrBSToAttrVector(boost::dynamic_bitset<unsigned long> &attrBS)
{	
	vector<int> ans;
	// //cout <<"BS = "<< attrBS <<"\n";

	for(int i = 0; i < attrBS.size(); i++)
	{
		if(attrBS[i])
			ans.push_back(i);
	}

	return ans;
}

boost::dynamic_bitset<unsigned long> attrVectorToAttrBS(vector<int> &attrVec)
{
	boost::dynamic_bitset<unsigned long> ans(attrInp.size());

	for(int i = 0; i < attrVec.size(); i++)
	{
		ans[attrVec[i]] = true;
	}
	
	// //cout<<"BS = "<< ans <<"\n";
	return ans;
}


vector<int> contextClosureBS(vector<int> &aset) 
{	
	totUpDownComputes++;
	boost::dynamic_bitset<unsigned long> aBS = attrVectorToAttrBS(aset), ansBS(attrInp.size());
	ansBS.set();

	int aid = -1;
	int osize = objInp.size() + 1;
	
	for (int i = 0; i < aset.size(); i++) 
	{
		if (attrInp[aset[i]].size() < osize) 
		{
			osize = attrInp[aset[i]].size();
			aid = aset[i];
		}
	}
			
	if(aid != -1)		
	{
		for (int i = 0; i < attrInp[aid].size(); i++) 
		{	
			int cObj = attrInp[aid][i];

			if(aBS.is_subset_of(objInpBS[cObj]))
			{
				ansBS &= objInpBS[cObj];
			}
		}
	}	

	else
	{
		for (int i = 0; i < objInp.size(); i++) 
		{	
			int cObj = i;
			ansBS &= objInpBS[cObj];
		}
	}

	return attrBSToAttrVector(ansBS);
}

vector<int> down(vector<int> &aset) {
	vector<int> ans;
	if (aset.size() == 0) {
		for (int i = 0; i < objInp.size(); i++) ans.push_back(i);
		return ans;
	}
	int aid = -1;
	int osize = objInp.size() + 1;
	for (int i = 0; i < aset.size(); i++) {
		if (attrInp[aset[i]].size() < osize) {
			osize = attrInp[aset[i]].size();
			aid = aset[i];
		}
	}
	for (int i = 0; i < attrInp[aid].size(); i++) {
		bool thisObj = true;
		int cObj = attrInp[aid][i];
		for (int j = 0; j < aset.size(); j++) {
			if (!binary_search(attrInp[aset[j]].begin(), attrInp[aset[j]].end(), cObj)) {
				thisObj = false;
				break;
			}
		}
		if (thisObj) ans.push_back(cObj);
	}
	return ans;
}

vector<int> up(vector<int> oset) {
	vector<int> ans;
	if (oset.size() == 0) {
		for (int i = 0; i < attrInp.size(); i++) ans.push_back(i);
		return ans;
	}
	int oid = -1;
	int asize = attrInp.size() + 1;
	for (int i = 0; i < oset.size(); i++) {
		if (objInp[oset[i]].size() < asize) {
			asize = objInp[oset[i]].size();
			oid = oset[i];
		}
	}
	for (int i = 0; i < objInp[oid].size(); i++) {
		bool thisAttr = true;
		int cattr = objInp[oid][i];
		for (int j = 0; j < oset.size(); j++) {
			if (!binary_search(objInp[oset[j]].begin(), objInp[oset[j]].end(), cattr)) {
				thisAttr = false;
				break;
			}
		}
		if (thisAttr) ans.push_back(cattr);
	}
	return ans;
}

//Can be used in case the input format is:
//Each line has the attribute numbers of attributes associated with the object represented by the line number.

void readFormalContext1(string fileName) {
	ifstream inFile(fileName);
	string line;
	while (getline(inFile, line)) {
		vector<int> cur;
		istringstream iss(line);
		int x;
		while (iss >> x) {
			if (x >= attrInp.size()) attrInp.resize(x + 1);
			attrInp[x].push_back(objInp.size());
			cur.push_back(x);
		}
		if (cur.size() != 0) objInp.push_back(cur);
	}
	//cout << "Done reading context\n";
	//cout << objInp.size() << " " << attrInp.size() << "\n";
	inFile.close();
}

//Can be used if the input format is:
//Line 1 contains number of objects
//Line 2 contains number of attributes
//There is a binary matrix from line 3 which represents the formal context, much like how we studied in class. 

void readFormalContext2(string fileName) {
	ifstream inFile(fileName);
	int obj, attr;
	inFile >> obj >> attr;
	objInp.resize(obj);
	attrInp.resize(attr);
	for (int i = 0; i < obj; i++) {
		int x;
		for (int j = 0; j < attr; j++) {
			inFile >> x;
			if (x == 1) {
				objInp[i].push_back(j);
				attrInp[j].push_back(i);
			}
		}
	}
	//cout << "Done reading formal context\n";
	//cout << objInp.size() << " " << attrInp.size() << "\n";
	inFile.close();
}

//Given L and X, find L(X).

vector<int> closure(vector<implication> &basis, vector<int> X) 
{	
	// auto start = chrono::high_resolution_clock::now();
	totClosureComputations++;
	if (basis.size() == 0) return X;
	vector<bool> cons;
	for (int i = 0; i <= basis.size(); i++) cons.push_back(false);
	bool changed = true;
	while (changed) {
		changed = false;
		for (int i = 0; i < basis.size(); i++) {
			if (cons[i] == true) continue;
			int isize = X.size();
			if (subvector(basis[i].lhs, X)) {
				cons[i] = true;
				X = vunion(basis[i].rhs, X);
			}
			if (X.size() != isize) {
				changed = true;
				break;
			}
		}
	}
	
	// auto end = chrono::high_resolution_clock::now();
	// totalClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
	return X;
}

vector<int> getRandomSubset(vector<int> &st)
{
	if(st.empty())
		return st;

	int numElems = st.size(), processedElems = 0;
	vector<int> ansSet;

	while(processedElems < numElems)
	{
		int bset = rand();

		for(int i = 0; i < 30; i++)
		{
			if(bset & (1 << i))
			{
				ansSet.push_back(st[processedElems]);
			}

			processedElems++;

			if(processedElems >= numElems)
				break;
		}
	}	

	return ansSet;	
}

vector<int> getFrequentAttrSet() 
{
	return getRandomSubset(objInp[discreteDistribution(re)]);
}

vector<int> getRandomAttrSet() 
{
	vector<int> ans;

	for (int i = 0; i < attrInp.size(); i++) 
	{
		ans.push_back(i);
	}

	return getRandomSubset(ans);
}

void getCounterExample(vector<implication> &basis, int s) 
{	
	double threadContextClosureTime = 0, threadImplicationClosureTime = 0;

	for (int i = s; i < maxTries && globalFlag; i += numThreads) 
	{	//Each thread handles an equal number of iterations. 
		totTries++;
		vector<int> X;

		if(frequentCounterExamples)
			X = getFrequentAttrSet();
		else
			X = getRandomAttrSet();

		auto start = chrono::high_resolution_clock::now();
		vector<int> cX = contextClosureBS(X);
		auto end = chrono::high_resolution_clock::now();
		threadContextClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
		
		if (X.size() == cX.size()) continue;		//It is sufficient to compare sizes since closure does not remove elements.
		
		start = chrono::high_resolution_clock::now();
		vector<int> cL = closure(basis, X);
		end = chrono::high_resolution_clock::now();
		threadImplicationClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();	

		if(threadContextClosureTime > thisIterMaxContextClosureTime)
			thisIterMaxContextClosureTime = threadContextClosureTime;

		if(threadImplicationClosureTime > thisIterMaxImplicationClosureTime)
			thisIterMaxImplicationClosureTime = threadImplicationClosureTime;

		if(epsilonStrong)
		{
			if(cX.size() != cL.size())
			{
				if (globalFlag) 
				{
					globalFlag = false;
					counterExample = cL;
					//cout << "Counter-example found after " << totTries << " tries \n";
					return;
				}
			}
		}

		else
		{
			if (cL.size() == X.size()) 
			{				//Same as above.
				if (globalFlag) 
				{
					globalFlag = false;
					counterExample = X;
					//cout << "Counter-example found after " << totTries << " tries \n";
					return;
				}
			}
		}	
	}
}

void tryPotentialCounterExamples(vector<implication> &basis)
{
	while(!potentialCounterExamples.empty())
	{
		vector <int> X = potentialCounterExamples.back();
		//cout <<"Trying a Potential Counter Example: ";
		printVector(X);
		potentialCounterExamples.pop_back();
		vector<int> cX = contextClosureBS(X);
		if (X.size() == cX.size()) continue;
		vector<int> cL = closure(basis, X);

		if(epsilonStrong)
		{
			if(cL.size() != cX.size())
			{
				//cout <<"It is a Counter Example!!\n";
				counterExample = cL;
				return;
			}
		}

		else
		{ 
			if(cL.size() == X.size())
			{	
				//cout <<"It is a Counter Example!!\n";
				counterExample = cL;
				return;
			}
		}
	}
}

vector<implication> generateImplicationBasis() 
{
	vector<implication> ans;
	while (true) 
	{
		auto start = chrono::high_resolution_clock::now();
		gCounter++;
		totTries = 0;
		//cout << "Going to get counter example. (Iteration Number: " << gCounter << " )" << endl;
		getLoopCount();
		//cout << "Max number of tries for this iteration: " << maxTries << "\n";
		globalFlag = true;
		counterExample.clear();
		thisIterMaxContextClosureTime = 0;
		thisIterMaxImplicationClosureTime = 0;

		if(!potentialCounterExamples.empty())
		{
			tryPotentialCounterExamples(ans);
			gCounter = 0;
		}

		if(counterExample.size() == 0)
		{
			vector<thread*> threadVector;
			for (int i = 1; i < numThreads; i++) {
				thread* tmp = new thread(getCounterExample, ref(ans), i);
				threadVector.push_back(tmp);
			}
			//
			//This is important. If we don't write the next statement,
			//the main thread will simply keep waiting without doing anything. 
			//This initially caused quite a bit of confusion, as a program without multi-threading was running faster
			//due to the main thread sitting idle.
			//
			getCounterExample(ans, 0);
			for (int i = 0; i < threadVector.size(); i++) {
				threadVector[i]->join();
			}
		}
		
		vector<int> X = counterExample;
		totCounterExamples++;
		updownTime += thisIterMaxContextClosureTime;
		totalClosureTime += thisIterMaxImplicationClosureTime;
		//cout << "Got counter example" << endl;
		auto end = std::chrono::high_resolution_clock::now();
		auto duration = chrono::duration_cast<chrono::microseconds>(end - start);
		//cout << duration.count() << "\n";
		totalTime += duration.count();
		if (X.size() == 0) break;
		bool found = false;
		start = chrono::high_resolution_clock::now();
		
		//The algorithm implemented as-is.
		for (int i = 0; i < ans.size(); i++) 
		{
			vector<int> A = ans[i].lhs;
			vector<int> B = ans[i].rhs;
			auto durBegin = chrono::high_resolution_clock::now();
			vector<int> C = intersection(A, X);
			auto durEnd = chrono::high_resolution_clock::now();
			intersectionTime += (chrono::duration_cast<chrono::microseconds>(durEnd - durBegin)).count();
			durBegin = chrono::high_resolution_clock::now();
			vector<int> cC = contextClosureBS(C);
			durEnd = chrono::high_resolution_clock::now();
			updownTime += (chrono::duration_cast<chrono::microseconds>(durEnd - durBegin)).count();

			if ((A.size() != C.size()) && (C.size() != cC.size())) {
				ans[i].lhs = C;
				ans[i].rhs = cC;
				found = true;
				break;
			}
		}
		if (!found) {
			ans.push_back(implication{ X, contextClosureBS(X) });
		}

		end = std::chrono::high_resolution_clock::now();
		totalExecTime2 += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
	}
	return ans;
}

void printUsageAndExit() 
{
	//cout << "Usage: ./algo <contextFileFullPath> <epsilon> <delta> <strong/weak> <uniform/frequent> [<numThreads>](Default = 1)\n";
	exit(0);
}

void fillPotentialCounterExamples()
{	
	// Two attribute sets 
	// for(int i = 0; i < attrInp.size(); i++)
	// {
	// 	for(int j = (i + 1); j < attrInp.size(); j++)
	// 	{
	// 		potentialCounterExamples.push_back({i, j});
	// 	}
	// }

	// Singleton
	for(int i = 0; i < attrInp.size(); i++)
	{
		potentialCounterExamples.push_back({i});
	}
}

void initializeObjInpBS()
{
	objInpBS.resize(objInp.size());

	for(int i = 0; i < objInp.size(); i++)
	{
		objInpBS[i] = attrVectorToAttrBS(objInp[i]);
	}				
}

int main(int argc, char** argv) 
{
	auto startTime = chrono::high_resolution_clock::now();
	srand(time(NULL));
	//cout <<"argc = "<< argc << "\n";

	if (argc != 6 && argc != 7) 
	{
		printUsageAndExit();
	}

	readFormalContext1(argv[1]);
	initializeObjInpBS();
	epsilon = atof(argv[2]);
	del = atof(argv[3]);
	if(string(argv[4]) == string("strong")) epsilonStrong = true;
	if(string(argv[5]) == string("frequent")) frequentCounterExamples = true;
	if(argc == 7) numThreads = atoi(argv[6]);

	fillPotentialCounterExamples();
	initializeRandSetGen();
	vector<implication> ans = generateImplicationBasis();
	//cout << totalTime << "\n";

	auto endTime = chrono::high_resolution_clock::now();
	double TotalExecTime = 0;
	TotalExecTime += (chrono::duration_cast<chrono::microseconds>(endTime - startTime)).count();
	cout << TotalExecTime <<",";
	cout << totalExecTime2 <<",";
	cout << totalClosureTime <<",";
	cout<< updownTime <<",";
	cout << totClosureComputations <<",";
	cout<< totUpDownComputes <<",";
	cout<< ans.size() <<",";
	cout<< totCounterExamples <<"\n";

	for (auto x : ans) {
		//cout << "Implication\n";
		printVector(x.lhs);
		printVector(x.rhs);
	}
	return 0;
}
