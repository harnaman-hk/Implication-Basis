#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>
#include <thread>
#include <mutex>          // std::mutex, std::unique_lock, std::defer_lock
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

typedef struct 
{
	boost::dynamic_bitset<unsigned long> lhs;
	boost::dynamic_bitset<unsigned long> rhs;
}implicationBS;

vector<vector<int>> objInp;			//For storing which attributes are associated with which objects
vector<vector<int>> attrInp;		//For storing which objects are associated with which attributes
vector<boost::dynamic_bitset<unsigned long> > objInpBS;
vector<int> frequencyOrderedAttributes;
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
boost::dynamic_bitset<unsigned long> counterExampleBS;
int gCounter = 0;					//For counting how many times the equivalence oracle has been used
int totTries = 0;	
long long sumTotTries = 0;
long long totClosureComputations = 0;
long long totUpDownComputes = 0;				//Stores how many random attribute sets needed to be tested before finding a counter-example. For debugging purposes. 
bool basisUpdate = false;
implicationBS updatedImplication;
int indexOfUpdatedImplication;
int implicationsSeen;
std::mutex mtx;           // mutex for critical section
vector<boost::dynamic_bitset<unsigned long> > potentialCounterExamplesBS;
double epsilon, del; 
bool epsilonStrong = false, frequentCounterExamples = false, bothCounterExamples = false;
int maxTries;						//Updated by getLoopCount() based on the value of gCounter, epsilon and delta.
bool implicationSupport = false;

std::random_device rd;
std::discrete_distribution<int> discreteDistribution;
std::default_random_engine re(rd());

vector<long double> attrSetWeight;
vector<implicationBS> ansBasisBS;

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
	maxTries =  (int)ceil(loopCount);
}

void printVector(vector<int> &A) 
{
	for (auto x : A) 
	{
		cout << x << " ";
	}

	cout << "\n";
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

boost::dynamic_bitset<unsigned long> contextClosureBS(boost::dynamic_bitset<unsigned long>  &aset) 
{	
	totUpDownComputes++;
	boost::dynamic_bitset<unsigned long> aBS = aset, ansBS(attrInp.size());
	ansBS.set();
	ansBS[0] = false;

	int aid = -1;
	int osize = objInp.size() + 1;
	
	for (int i = 0; i < aset.size(); i++) 
	{	
		if(aset[i] && (attrInp[i].size() < osize)) 
		{
			osize = attrInp[i].size();
			aid = i;
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

	return ansBS;
}

//Given L and X, find L(X).
boost::dynamic_bitset<unsigned long> closureBS(vector<implicationBS> &basis, boost::dynamic_bitset<unsigned long> X) 
{	
	totClosureComputations++;
	if (basis.size() == 0) return X;
	vector<bool> cons;
	for (int i = 0; i <= basis.size(); i++) cons.push_back(false);
	bool changed = true;
	
	while(changed) 
	{
		changed = false;
		
		for (int i = 0; i < basis.size(); i++) 
		{
			if (cons[i] == true) continue;
			
			if (basis[i].lhs.is_subset_of(X)) 
			{
				cons[i] = true;

				if(!basis[i].rhs.is_subset_of(X))
				{
					X |= basis[i].rhs;
					changed = true;
					break;
				}	
			}
		}
	}
	
	return X;
}

boost::dynamic_bitset<unsigned long> getRandomSubsetBS(boost::dynamic_bitset<unsigned long> &st)
{
	int numElems = st.size(), processedElems = 0;
	boost::dynamic_bitset<unsigned long> ansSet(numElems);

	while(processedElems < numElems)
	{
		int bset = rand();

		for(int i = 0; i < 30; i++)
		{
			if((bset & (1 << i)) && (st[processedElems]))
			{
				ansSet[processedElems] = true;
			}

			processedElems++;

			if(processedElems >= numElems)
				break;
		}
	}	

	return ansSet;	
}

boost::dynamic_bitset<unsigned long> getFrequentAttrSetBS() 
{
	return getRandomSubsetBS(objInpBS[discreteDistribution(re)]);
}

boost::dynamic_bitset<unsigned long> getRandomAttrSetBS() 
{
	boost::dynamic_bitset<unsigned long> ans(attrInp.size());
	ans.set();
	ans[0] = false;
	return getRandomSubsetBS(ans);
}

void getCounterExample(vector<implicationBS> &basis, int s) 
{	
	double threadContextClosureTime = 0, threadImplicationClosureTime = 0;
	std::unique_lock<std::mutex> lck (mtx,std::defer_lock);

	for (int i = s; i < maxTries && globalFlag; i += numThreads) 
	{	//Each thread handles an equal number of iterations. 
		lck.lock();
		totTries++;
  		lck.unlock();
		boost::dynamic_bitset<unsigned long> X;

		if(frequentCounterExamples)
			X = getFrequentAttrSetBS();
		else
			X = getRandomAttrSetBS();

		auto start = chrono::high_resolution_clock::now();
		boost::dynamic_bitset<unsigned long> cX = contextClosureBS(X);
		auto end = chrono::high_resolution_clock::now();
		threadContextClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
		
		if (X.count() == cX.count()) continue;		//It is sufficient to compare sizes since closure does not remove elements.
		
		start = chrono::high_resolution_clock::now();
		boost::dynamic_bitset<unsigned long> cL = closureBS(basis, X);
		end = chrono::high_resolution_clock::now();
		threadImplicationClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();	

		lck.lock();
		
		if(threadContextClosureTime > thisIterMaxContextClosureTime)
			thisIterMaxContextClosureTime = threadContextClosureTime;

		if(threadImplicationClosureTime > thisIterMaxImplicationClosureTime)
			thisIterMaxImplicationClosureTime = threadImplicationClosureTime;
		
		lck.unlock();
		
		if(epsilonStrong)
		{
			if(cX.count() != cL.count())
			{
				if (globalFlag) 
				{
					globalFlag = false;
					counterExampleBS = cL;
					//cout << "Counter-example found after " << totTries << " tries \n";
					return;
				}
			}
		}

		else
		{
			if (cL.count() == X.count()) 
			{				//Same as above.
				if (globalFlag) 
				{
					globalFlag = false;
					counterExampleBS = X;
					//cout << "Counter-example found after " << totTries << " tries \n";
					return;
				}
			}
		}	
	}
}

void tryPotentialCounterExamples(vector<implicationBS> &basis)
{
	while(!potentialCounterExamplesBS.empty())
	{
		boost::dynamic_bitset<unsigned long> X = potentialCounterExamplesBS.back();
		//cout <<"Trying a Potential Counter Example: ";
		//printVector(X);
		potentialCounterExamplesBS.pop_back();
		boost::dynamic_bitset<unsigned long> cX = contextClosureBS(X);
		if (X.count() == cX.count()) continue;
		boost::dynamic_bitset<unsigned long> cL = closureBS(basis, X);

		if(epsilonStrong)
		{
			if(cL.count() != cX.count())
			{
				//cout <<"It is a Counter Example!!\n";
				counterExampleBS = cL;
				globalFlag = false;
				return;
			}
		}

		else
		{ 
			if(cL.count() == X.count())
			{	
				//cout <<"It is a Counter Example!!\n";
				counterExampleBS = cL;
				globalFlag = false;
				return;
			}
		}
	}
}

void tryToUpdateImplicationBasis(vector<implicationBS> &basis)
{	
	std::unique_lock<std::mutex> lck (mtx,std::defer_lock);
	double threadContextClosureTime = 0;
	lck.lock();

	while((implicationsSeen < basis.size()) && (!basisUpdate))
	{
		boost::dynamic_bitset<unsigned long> A = basis[implicationsSeen].lhs;
		boost::dynamic_bitset<unsigned long> B = basis[implicationsSeen].rhs;
		int curIndex = implicationsSeen;
		implicationsSeen++;
		lck.unlock();
		boost::dynamic_bitset<unsigned long> C = A & counterExampleBS;
		auto durBegin = chrono::high_resolution_clock::now();
		boost::dynamic_bitset<unsigned long> cC = contextClosureBS(C);
		auto durEnd = chrono::high_resolution_clock::now();
		threadContextClosureTime += (chrono::duration_cast<chrono::microseconds>(durEnd - durBegin)).count();

		if ((A.count() != C.count()) && (C.count() != cC.count())) 
		{	
			lck.lock();

			if(!basisUpdate)
			{
				basisUpdate = true;
				indexOfUpdatedImplication = curIndex;
				updatedImplication.lhs = C;
				updatedImplication.rhs = cC;
			}	

			else if(basisUpdate && (curIndex < indexOfUpdatedImplication))
			{
				indexOfUpdatedImplication = curIndex;
				updatedImplication.lhs = C;
				updatedImplication.rhs = cC;
			}

			lck.unlock();
		}

		lck.lock();
	}

	if(threadContextClosureTime > thisIterMaxContextClosureTime)
		thisIterMaxContextClosureTime = threadContextClosureTime;
	
	lck.unlock();
}

vector<implication> BSBasisToVectorBasis(vector<implicationBS> ansBS)
{
	vector<implication> ans;

	for(int i = 0; i < ansBS.size(); i++)
	{
		ans.push_back(implication{attrBSToAttrVector(ansBS[i].lhs), attrBSToAttrVector(ansBS[i].rhs)});
	}

	return ans;
}

vector<implication> generateImplicationBasis() 
{
	vector<implicationBS> ansBS;

	while (true) 
	{	
		auto start = chrono::high_resolution_clock::now();
		gCounter++;
		totTries = 0;
		//cout << "Going to get counter example. (Iteration Number: " << gCounter << " )" << endl;
		getLoopCount();
		//cout << "Max number of tries for this iteration: " << maxTries << "\n";
		globalFlag = true;
		counterExampleBS.clear();
		thisIterMaxContextClosureTime = 0;
		thisIterMaxImplicationClosureTime = 0;

		if(!potentialCounterExamplesBS.empty())
		{
			tryPotentialCounterExamples(ansBS);
			gCounter = 0;
		}

		if(globalFlag)
		{
			vector<thread*> threadVector;
			for (int i = 1; i < numThreads; i++) {
				thread* tmp = new thread(getCounterExample, ref(ansBS), i);
				threadVector.push_back(tmp);
			}
			//
			//This is important. If we don't write the next statement,
			//the main thread will simply keep waiting without doing anything. 
			//This initially caused quite a bit of confusion, as a program without multi-threading was running faster
			//due to the main thread sitting idle.
			//
			getCounterExample(ansBS, 0);
			for (int i = 0; i < threadVector.size(); i++) {
				threadVector[i]->join();
			}
		}

		updownTime += thisIterMaxContextClosureTime;
		totalClosureTime += thisIterMaxImplicationClosureTime;

		if(globalFlag && bothCounterExamples)
		{
			bothCounterExamples = false;
			frequentCounterExamples = false;
			gCounter = max(0, gCounter - 1);
			continue;
		}

		sumTotTries += totTries;
		if (globalFlag) break;

		boost::dynamic_bitset<unsigned long> X = counterExampleBS;
		//printVector(X);
		totCounterExamples++;
		//cout << "Got counter example" << endl;
		auto end = std::chrono::high_resolution_clock::now();
		auto duration = chrono::duration_cast<chrono::microseconds>(end - start);
		//cout << duration.count() << "\n";
		totalTime += duration.count();
		bool found = false;
		start = chrono::high_resolution_clock::now();
		basisUpdate = false;
		implicationsSeen = 0;
		thisIterMaxContextClosureTime = 0;
		
		//The algorithm implemented as-is.
		vector<thread*> threads(numThreads);

		for(int i = 1; i < numThreads; i++)
			threads[i] = new thread(tryToUpdateImplicationBasis, ref(ansBS));

		tryToUpdateImplicationBasis(ansBS);

		for(int i = 1; i < numThreads; i++)
			threads[i]->join();	
		
		updownTime += thisIterMaxContextClosureTime;

		if (!basisUpdate) 
			ansBS.push_back(implicationBS{ X, contextClosureBS(X)});
		else
			ansBS[indexOfUpdatedImplication] = updatedImplication;

		end = std::chrono::high_resolution_clock::now();
		totalExecTime2 += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
	}

	ansBasisBS = ansBS;
	return BSBasisToVectorBasis(ansBS);
}

void printUsageAndExit() 
{
	cout << "Usage: ./algo <contextFileFullPath> <epsilon> <delta> <strong/weak> <uniform/frequent/both> <numThreads> <support/none>\n";
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
	for(int i = 1; i < attrInp.size(); i++)
	{	
		vector <int> cVec = {i};
		potentialCounterExamplesBS.push_back(attrVectorToAttrBS(cVec));
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

bool isLectGreater(boost::dynamic_bitset<unsigned long> &closedSet, int lectInd)
{
	for(int i = 0; i <= lectInd; i++)
		if(closedSet[frequencyOrderedAttributes[i]])
			return true;

	return false;		
}

boost::dynamic_bitset<unsigned long> nextContextClosure(boost::dynamic_bitset<unsigned long> A, boost::dynamic_bitset<unsigned long> finalClosedSet)
{
	int nAttr = attrInp.size() - 1;

	for(int i = nAttr; i > 0; i--)
	{
		if(A[frequencyOrderedAttributes[i]])
			A[frequencyOrderedAttributes[i]] = false;
		else
		{
			boost::dynamic_bitset<unsigned long> B, temp = A;
			temp[frequencyOrderedAttributes[i]] = true;
			B = contextClosureBS(temp);

			bool flag = true;

			for(int j = 1; j < i; j++)
			{
				if(B[frequencyOrderedAttributes[j]] & (!A[frequencyOrderedAttributes[j]]))
				{
					flag = false;
					break;
				}
			}

			if(flag)
				return B;
		}	
	}

	return finalClosedSet;
}

int allContextClosures()
{	
	return 50;
	int totalClosedSets = 1;
	boost::dynamic_bitset<unsigned long> currentClosedSet, finalClosedSet(attrInp.size()), emptySet(attrInp.size());
	currentClosedSet = contextClosureBS(emptySet);
	finalClosedSet.set();
	finalClosedSet[0] = false;
	int nattr = attrInp.size();
	int lectInd = max(1, ((3 * nattr) / 4)), lectLessClosures;
	bool lectDone = false;
	auto timeStart = chrono::high_resolution_clock::now();
	auto timePrev = chrono::high_resolution_clock::now();

	while(currentClosedSet != finalClosedSet)
	{
		currentClosedSet = nextContextClosure(currentClosedSet, finalClosedSet);
		totalClosedSets++;
		auto timeNow = chrono::high_resolution_clock::now();
		double duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timePrev)).count();

		if(duration > 60000000)
		{
			// cout <<"Total Context closures till now: "<< totalClosedSets << endl;
			timePrev = timeNow;
		}

		if((!lectDone) && isLectGreater(currentClosedSet, lectInd))
		{
			lectLessClosures = totalClosedSets;
			lectDone = true;
		}

		duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timeStart)).count();

		if(lectDone && (duration > 6000000))
		{
			// cout <<"Lectically less Context Closures:"<< lectLessClosures << endl;
			return lectLessClosures;
		}
	}

	// cout <<"Lectically less Context Closures:"<< lectLessClosures << endl;
	return lectLessClosures;
}

boost::dynamic_bitset<unsigned long> nextImplicationClosure(boost::dynamic_bitset<unsigned long> A, boost::dynamic_bitset<unsigned long> finalClosedSet)
{
	int nAttr = attrInp.size() - 1;

	for(int i = nAttr; i > 0; i--)
	{
		if(A[frequencyOrderedAttributes[i]])
			A[frequencyOrderedAttributes[i]] = false;
		else
		{
			boost::dynamic_bitset<unsigned long> B, temp = A;
			temp[frequencyOrderedAttributes[i]] = true;
			B = closureBS(ansBasisBS, temp);

			bool flag = true;

			for(int j = 1; j < i; j++)
			{
				if(B[frequencyOrderedAttributes[j]] & (!A[frequencyOrderedAttributes[j]]))
				{
					flag = false;
					break;
				}
			}

			if(flag)
				return B;
		}	
	}

	return finalClosedSet;
}

int allImplicationClosures()
{
	int totalClosedSets = 1;
	boost::dynamic_bitset<unsigned long> currentClosedSet, finalClosedSet(attrInp.size()), emptySet(attrInp.size());
	currentClosedSet = closureBS(ansBasisBS, emptySet);
	finalClosedSet.set();
	finalClosedSet[0] = false;
	
	int nattr = attrInp.size();
	int lectInd = max(1, ((1 * nattr) / 2)), lectLessClosures;
	bool lectDone = false;
	auto timeStart = chrono::high_resolution_clock::now();
	auto timePrev = chrono::high_resolution_clock::now();

	while(currentClosedSet != finalClosedSet)
	{
		currentClosedSet = nextImplicationClosure(currentClosedSet, finalClosedSet);
		totalClosedSets++;

		auto timeNow = chrono::high_resolution_clock::now();
		double duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timePrev)).count();

		if(duration > 60000000)
		{
			// cout <<"Total Implication closures till now: "<< totalClosedSets << endl;
			timePrev = timeNow;
		}

		if((!lectDone) && isLectGreater(currentClosedSet, lectInd))
		{
			lectLessClosures = totalClosedSets;
			lectDone = true;
		}

		duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timeStart)).count();

		if(lectDone && (duration > 6000000))
		{
			// cout <<"Lectically less Implication Closures:"<< lectLessClosures << endl;
			return lectLessClosures;
		}
	}

	// cout <<"Lectically less Implication Closures:"<< lectLessClosures << endl;
	return lectLessClosures;
}

void getSupportOfImplications()
{	
	vector<int> supports;

	for(int i = 0; i < ansBasisBS.size(); i++)
	{
		int support = 0;

		for(int j = 0; j < objInpBS.size(); j++)
		{
			if(ansBasisBS[i].lhs.is_subset_of(objInpBS[j]))
				support++;
		}

		supports.push_back(support);
	}

	sort(supports.rbegin(), supports.rend());

	for(auto it:supports)
		cout << it <<"\n";

	return;
}

void initFrequencyOrderedAttributes()
{
	vector <int> freqAttr(attrInp.size(), 0);

	for(int i = 0; i < objInp.size(); i++)
	{
		for(int j = 0; j < objInp[i].size(); j++)
			freqAttr[objInp[i][j]]++;
	}

	vector<pair<int, int> > freqPairs;

	for(int i = 1; i < attrInp.size(); i++)
	{
		freqPairs.push_back({freqAttr[i], i});
	}

	sort(freqPairs.begin(), freqPairs.end());
	frequencyOrderedAttributes.push_back(0);

	for(int i = 0; i < freqPairs.size(); i++)
		frequencyOrderedAttributes.push_back(freqPairs[i].second);

}

int main(int argc, char** argv) 
{
	auto startTime = chrono::high_resolution_clock::now();
	srand(time(NULL));
	//cout <<"argc = "<< argc << "\n";

	if (argc != 8) 
	{
		printUsageAndExit();
	}

	readFormalContext1(argv[1]);
	initializeObjInpBS();
	initFrequencyOrderedAttributes();
	epsilon = atof(argv[2]);
	del = atof(argv[3]);
	if(string(argv[4]) == string("strong")) epsilonStrong = true;
	if(string(argv[5]) == string("frequent")) frequentCounterExamples = true;
	if(string(argv[5]) == string("both")) bothCounterExamples = true;
	if(bothCounterExamples) frequentCounterExamples = true;
	numThreads = atoi(argv[6]);
	if(string(argv[7]) == string("support")) implicationSupport = true;

	fillPotentialCounterExamples();
	initializeRandSetGen();
	vector<implication> ans = generateImplicationBasis();
	// cout << totalTime << "\n";

	auto endTime = chrono::high_resolution_clock::now();
	double TotalExecTime = 0;
	TotalExecTime += (chrono::duration_cast<chrono::microseconds>(endTime - startTime)).count();
	
	if(implicationSupport)
	{
		getSupportOfImplications();
		return 0;
	}

	for(int i = 2; i < 7; i++)
		cout << argv[i] <<",";

	cout << TotalExecTime <<",";
	cout << totalExecTime2 <<",";
	cout << totalClosureTime <<",";
	cout << updownTime <<",";
	cout << totClosureComputations <<",";
	cout<< totUpDownComputes <<",";
	cout<< ans.size() <<",";
	cout<< totCounterExamples <<",";
	cout<< sumTotTries <<",";
	cout<< allContextClosures() <<","; 
	cout<< allImplicationClosures()<<"\n";

	for (auto x : ans) {
		// //cout << "Implication\n";
		printVector(x.lhs);
		printVector(x.rhs);
	}
	return 0;
}
