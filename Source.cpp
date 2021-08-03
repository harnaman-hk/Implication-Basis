#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>
#include <thread>
#include <mutex> // std::mutex, std::unique_lock, std::defer_lock
#include <set>
#include <time.h>
#include <stdlib.h>
#include <chrono>
#include <cmath>
#include <random>
#include <unordered_set>
#include <boost/dynamic_bitset.hpp>
#include "ThreadPool.h"

using namespace std;

typedef struct s
{
	vector<int> lhs;
	vector<int> rhs;
} implication;

typedef struct
{
	boost::dynamic_bitset<unsigned long> lhs;
	boost::dynamic_bitset<unsigned long> rhs;
} implicationBS;

#define TIMEPRINT(X) (((double)X) / ((double)1000000))

vector<vector<int>> objInp;	 //For storing which attributes are associated with which objects
vector<vector<int>> attrInp; //For storing which objects are associated with which attributes
vector<boost::dynamic_bitset<unsigned long>> objInpBS;
vector<int> frequencyOrderedAttributes;
double totalTime = 0;
double totalExecTime2 = 0; //Stores total time spent generating counter examples
double totalClosureTime = 0;
double intersectionTime = 0;
double thisIterMaxImplicationClosureTime = 0;
double thisIterMaxContextClosureTime = 0;
double updownTime = 0;
int numThreads = 1, maxThreads;
long long totCounterExamples = 0;
bool globalFlag; //For terminating other threads in case one thread found a counter-example
boost::dynamic_bitset<unsigned long> counterExampleBS;
bool isPositiveCounterExample = true;
int gCounter = 0; //For counting how many times the equivalence oracle has been used
int totTries = 0;
long long sumTotTries = 0;
long long totClosureComputations = 0;
long long totUpDownComputes = 0; //Stores how many random attribute sets needed to be tested before finding a counter-example. For debugging purposes.
bool basisUpdate = false;
long long countPositiveCounterExample = 0, countNegativeCounterExample = 0;
implicationBS updatedImplication;
int indexOfUpdatedImplication;
int implicationsSeen;
std::mutex mtx; // mutex for critical section
vector<boost::dynamic_bitset<unsigned long>> potentialCounterExamplesBS;
double epsilon, del;
bool epsilonStrong = false, frequentCounterExamples = false, bothCounterExamples = false;
int maxTries; //Updated by getLoopCount() based on the value of gCounter, epsilon and delta.
bool implicationSupport = false;
bool emptySetClosureComputed = false;
boost::dynamic_bitset<unsigned long> emptySetClosure;
long long emptySetClosureComputes = 0;
long long aEqualToCCount = 0;

std::random_device rd;
std::discrete_distribution<int> discreteDistribution, discreteDistributionArea;
std::discrete_distribution<long long> discreteDistributionSquared;
std::discrete_distribution<long long> discreteDistributionDiscriminativity;
std::binomial_distribution<int> binomialDistribution;
std::default_random_engine re(rd());

vector<std::discrete_distribution<int>> discreteDistributionAttributeSets;
vector<int> objectLabels, positiveObjects, negativeObjects;
vector<long double> attrSetWeight;
vector<implicationBS> ansBasisBS;
vector<pair<int, implicationBS>> updatedImplications;

double threadOverheadTime = 6;
double prevIterTime = 0;
int UpdateImplicationTries = 0;
int prevThreads = 1;
int singletonCounterexamples = 0;
//Can be used in case the input format is:
//Each line has the attribute numbers of attributes associated with the object represented by the line number.
int counterexampleType = 1;

void readFormalContext1(string fileName)
{
	ifstream inFile(fileName);
	string line;
	while (getline(inFile, line))
	{
		vector<int> cur;
		istringstream iss(line);
		int x;
		while (iss >> x)
		{
			if (x >= attrInp.size())
				attrInp.resize(x + 1);
			attrInp[x].push_back(objInp.size());
			cur.push_back(x);
		}
		if (cur.size() != 0)
			objInp.push_back(cur);
	}
	//cout << "Done reading context\n";
	//cout << objInp.size() << " " << attrInp.size() << "\n";
	inFile.close();
}

//Can be used if the input format is:
//Line 1 contains number of objects
//Line 2 contains number of attributes
//There is a binary matrix from line 3 which represents the formal context, much like how we studied in class.

void readFormalContext2(string fileName)
{
	ifstream inFile(fileName);
	int obj, attr;
	inFile >> obj >> attr;
	objInp.resize(obj);
	attrInp.resize(attr);
	for (int i = 0; i < obj; i++)
	{
		int x;
		for (int j = 0; j < attr; j++)
		{
			inFile >> x;
			if (x == 1)
			{
				objInp[i].push_back(j);
				attrInp[j].push_back(i);
			}
		}
	}
	//cout << "Done reading formal context\n";
	//cout << objInp.size() << " " << attrInp.size() << "\n";
	inFile.close();
}

void readLabels(string labelFile)
{
	ifstream labelInput(labelFile);
	int temp;
	int oID = 0;

	while (labelInput >> temp)
	{
		objectLabels.push_back(temp);

		if (temp == 0)
			negativeObjects.push_back(oID);
		else
			positiveObjects.push_back(oID);

		oID++;
	}

	labelInput.close();
}

long double nChooseK(long long n, long long k)
{
	long double res = 1;
	for (long long i = 1; i <= k; ++i)
		res = res * ((long double)(n - k + i)) / ((long double)i);
	return res;
}

void initializeRandSetGen()
{
	vector<long double> powersOfTwo(attrInp.size() + 2);
	powersOfTwo[0] = 1;

	for (int i = 1; i < powersOfTwo.size(); i++)
		powersOfTwo[i] = ((long double)2) * powersOfTwo[i - 1];

	attrSetWeight.resize(objInp.size());

	for (int i = 0; i < objInp.size(); i++)
	{
		attrSetWeight[i] = powersOfTwo[objInp[i].size()];
	}

	discreteDistribution = std::discrete_distribution<int>(attrSetWeight.begin(), attrSetWeight.end());

	if (counterexampleType == 2)
	{
		for (int i = 0; i < objInp.size(); i++)
		{
			attrSetWeight[i] *= ((long double)objInp[i].size()) * ((long double)0.5);
		}

		discreteDistributionArea = std::discrete_distribution<int>(attrSetWeight.begin(), attrSetWeight.end());

		discreteDistributionAttributeSets.resize(attrInp.size() + 2);

		for (int i = 0; i < discreteDistributionAttributeSets.size(); i++)
		{
			vector<long double> nChooseKWeights(i + 1);

			for (int j = 0; j <= i; j++)
			{
				nChooseKWeights[j] = nChooseK(i, j);
			}

			discreteDistributionAttributeSets[i] = std::discrete_distribution<int>(nChooseKWeights.begin(), nChooseKWeights.end());
		}
	}

	if (counterexampleType == 3)
	{
		long long numObj = objInp.size();
		vector<long double> weights(numObj * numObj);
		long long size = 0;

		for (long long i = 0; i < numObj; i++)
		{
			for (long long j = 0; j < numObj; j++)
			{
				long double power = (objInpBS[i] & objInpBS[j]).count();
				weights[size] = powersOfTwo[power];
				size++;
			}
		}

		discreteDistributionSquared = std::discrete_distribution<long long>(weights.begin(), weights.end());
	}

	if (counterexampleType == 4)
	{
		long long numObj = objInp.size();
		vector<long double> weights(numObj * numObj);
		long long size = 0;

		for (long long i = 0; i < numObj; i++)
		{
			for (long long j = 0; j < numObj; j++)
			{
				long double power = 0;

				if ((objectLabels[i] == 0) && (objectLabels[j] == 1))
				{
					power = powersOfTwo[(objInpBS[i] - objInpBS[j]).count()];
					power = (power - 1) * powersOfTwo[(objInpBS[i] & objInpBS[j]).count()];
				}

				weights[size] = power;
				size++;
			}
		}

		discreteDistributionDiscriminativity = std::discrete_distribution<long long>(weights.begin(), weights.end());
	}

	if (counterexampleType == 5)
	{
		int n = objInp.size();
		float p = 0.2;
		binomialDistribution = std::binomial_distribution<int>(n, p);
		// cout << "\nGenerated binomial dist with n = " << n << ", p = " << p << "\n";
	}
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
		cout << x << " ";
	}
}

vector<int> attrBSToAttrVector(boost::dynamic_bitset<unsigned long> &attrBS)
{
	vector<int> ans;
	// //cout <<"BS = "<< attrBS <<"\n";

	for (int i = 0; i < attrBS.size(); i++)
	{
		if (attrBS[i])
			ans.push_back(i);
	}

	return ans;
}

boost::dynamic_bitset<unsigned long> attrVectorToAttrBS(vector<int> &attrVec)
{
	boost::dynamic_bitset<unsigned long> ans(attrInp.size());

	for (int i = 0; i < attrVec.size(); i++)
	{
		ans[attrVec[i]] = true;
	}

	// //cout<<"BS = "<< ans <<"\n";
	return ans;
}

boost::dynamic_bitset<unsigned long> contextClosureBS(boost::dynamic_bitset<unsigned long> &aset)
{
	totUpDownComputes++;
	boost::dynamic_bitset<unsigned long> aBS = aset, ansBS(attrInp.size());
	ansBS.set();
	ansBS[0] = false;

	int aid = -1;
	int osize = objInp.size() + 1;

	for (int i = 0; i < aset.size(); i++)
	{
		if (aset[i] && (attrInp[i].size() < osize))
		{
			osize = attrInp[i].size();
			aid = i;
		}
	}

	if (aid != -1)
	{
		for (int i = 0; i < attrInp[aid].size(); i++)
		{
			int cObj = attrInp[aid][i];

			if (aBS.is_subset_of(objInpBS[cObj]))
			{
				ansBS &= objInpBS[cObj];
			}

			// if(ansBS.count() == aBS.count())
			// 	return ansBS;
		}
	}

	else
	{
		emptySetClosureComputes++;

		if (emptySetClosureComputed)
			return emptySetClosure;

		for (int i = 0; i < objInp.size(); i++)
		{
			int cObj = i;
			ansBS &= objInpBS[cObj];
		}

		emptySetClosure = ansBS;
		emptySetClosureComputed = true;
	}

	return ansBS;
}

//Given L and X, find L(X).
boost::dynamic_bitset<unsigned long> closureBS(vector<implicationBS> &basis, boost::dynamic_bitset<unsigned long> X)
{
	totClosureComputations++;
	if (basis.size() == 0)
		return X;
	vector<bool> cons;
	for (int i = 0; i <= basis.size(); i++)
		cons.push_back(false);
	bool changed = true;

	while (changed)
	{
		changed = false;

		for (int i = 0; i < basis.size(); i++)
		{
			if (cons[i] == true)
				continue;

			if (basis[i].lhs.is_subset_of(X))
			{
				cons[i] = true;

				if (!basis[i].rhs.is_subset_of(X))
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

bool isSetEqualToImpCLosure(vector<implicationBS> &basis, boost::dynamic_bitset<unsigned long> &X)
{
	for (int i = 0; i < basis.size(); i++)
	{
		if (basis[i].lhs.is_subset_of(X) && (!basis[i].rhs.is_subset_of(X)))
			return false;
	}

	return true;
}

boost::dynamic_bitset<unsigned long> getRandomSubsetBS(boost::dynamic_bitset<unsigned long> &st)
{
	int numElems = st.size(), processedElems = 0;
	boost::dynamic_bitset<unsigned long> ansSet(numElems);

	while (processedElems < numElems)
	{
		int bset = rand();

		for (int i = 0; i < 30; i++)
		{
			if ((bset & (1 << i)) && (st[processedElems]))
			{
				ansSet[processedElems] = true;
			}

			processedElems++;

			if (processedElems >= numElems)
				break;
		}
	}

	return ansSet;
}

boost::dynamic_bitset<unsigned long> getFrequentAttrSetBS()
{
	// cout <<"1\n";
	if (counterexampleType == 1)
		return getRandomSubsetBS(objInpBS[discreteDistribution(re)]);
	if (counterexampleType == 2)
	{
		// cout <<"2--\n";
		int objId = discreteDistributionArea(re);
		int objSize = objInp[objId].size();
		vector<int> object = objInp[objId];
		int setSize = discreteDistributionAttributeSets[objSize](re);
		vector<int> indices(objSize);

		for (int i = 0; i < objSize; i++)
			indices[i] = i;

		shuffle(indices.begin(), indices.end(), re);
		boost::dynamic_bitset<unsigned long> ans(attrInp.size());

		for (int i = 0; i < setSize; i++)
		{
			ans[object[indices[i]]] = true;
		}

		return ans;
	}

	if (counterexampleType == 3)
	{
		// cout <<"3--\n";
		long long intersectionId = discreteDistributionSquared(re);
		long long set1 = intersectionId / (long long)objInp.size();
		long long set2 = intersectionId % (long long)objInp.size();
		boost::dynamic_bitset<unsigned long> tempSet = objInpBS[set1] & objInpBS[set2];
		return getRandomSubsetBS(tempSet);
	}

	if (counterexampleType == 4)
	{
		long long intersectionId = discreteDistributionDiscriminativity(re);
		long long set1 = intersectionId / (long long)objInp.size();
		long long set2 = intersectionId % (long long)objInp.size();
		boost::dynamic_bitset<unsigned long> tempSet1 = objInpBS[set1] - objInpBS[set2],
											 tempSet2 = objInpBS[set1] & objInpBS[set2];
		boost::dynamic_bitset<unsigned long> setF = getRandomSubsetBS(tempSet1),
											 setFp = getRandomSubsetBS(tempSet2);
		return (setF | setFp);
	}

	if (counterexampleType == 5)
	{
		return getRandomSubsetBS(objInpBS[binomialDistribution(re)]);
	}
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
	std::unique_lock<std::mutex> lck(mtx, std::defer_lock);
	int threadTries = 0;
	boost::dynamic_bitset<unsigned long> X;

	for (int i = s; i < maxTries && globalFlag; i += numThreads)
	{ //Each thread handles an equal number of iterations.
		threadTries++;

		if (frequentCounterExamples)
			X = getFrequentAttrSetBS();
		else
			X = getRandomAttrSetBS();

		auto start = chrono::high_resolution_clock::now();
		boost::dynamic_bitset<unsigned long> cX = contextClosureBS(X);
		auto end = chrono::high_resolution_clock::now();
		threadContextClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();

		start = chrono::high_resolution_clock::now();
		boost::dynamic_bitset<unsigned long> cL = closureBS(basis, X);
		end = chrono::high_resolution_clock::now();
		threadImplicationClosureTime += (chrono::duration_cast<chrono::microseconds>(end - start)).count();

		if (epsilonStrong)
		{
			if (!cL.is_subset_of(cX))
			{
				lck.lock();
				globalFlag = false;
				counterExampleBS = cX;
				isPositiveCounterExample = true;
				lck.unlock();
				break;
			}

			if (!cX.is_subset_of(cL))
			{
				lck.lock();
				globalFlag = false;
				counterExampleBS = cL;
				isPositiveCounterExample = false;
				lck.unlock();
				break;
			}
		}

		else
		{
			if (X.count() == cX.count())
			{
				if (!isSetEqualToImpCLosure(basis, X))
				{
					lck.lock();
					globalFlag = false;
					counterExampleBS = X;
					isPositiveCounterExample = true;
					lck.unlock();
					break;
				}
			}
			else
			{
				if (isSetEqualToImpCLosure(basis, X))
				{
					lck.lock();
					globalFlag = false;
					counterExampleBS = X;
					isPositiveCounterExample = false;
					lck.unlock();
					break;
				}
			}
		}
	}

	lck.lock();

	totTries += threadTries;

	if (threadContextClosureTime > thisIterMaxContextClosureTime)
		thisIterMaxContextClosureTime = threadContextClosureTime;

	if (threadImplicationClosureTime > thisIterMaxImplicationClosureTime)
		thisIterMaxImplicationClosureTime = threadImplicationClosureTime;

	lck.unlock();
}

void tryPotentialCounterExamples(vector<implicationBS> &basis)
{
	while (!potentialCounterExamplesBS.empty())
	{
		boost::dynamic_bitset<unsigned long> X = potentialCounterExamplesBS.back();
		//cout <<"Trying a Potential Counter Example: ";
		//printVector(X);
		potentialCounterExamplesBS.pop_back();
		boost::dynamic_bitset<unsigned long> cX = contextClosureBS(X);
		if (X.count() == cX.count())
			continue;
		boost::dynamic_bitset<unsigned long> cL = closureBS(basis, X);

		if (epsilonStrong)
		{
			if (cL.count() != cX.count())
			{
				//cout <<"It is a Counter Example!!\n";
				counterExampleBS = cL;
				globalFlag = false;
				return;
			}
		}

		else
		{
			if (cL.count() == X.count())
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
	std::unique_lock<std::mutex> lck(mtx, std::defer_lock);
	double threadContextClosureTime = 0;
	lck.lock();
	if (isPositiveCounterExample)
	{
		while (implicationsSeen < basis.size())
		{
			UpdateImplicationTries++;
			int currIndex = implicationsSeen;
			boost::dynamic_bitset<unsigned long> A = basis[currIndex].lhs;
			boost::dynamic_bitset<unsigned long> B = basis[currIndex].rhs;
			implicationsSeen++;
			lck.unlock();
			if (A.is_subset_of(counterExampleBS) && !B.is_subset_of(counterExampleBS))
			{
				lck.lock();
				updatedImplications.push_back({currIndex, implicationBS({A, B & counterExampleBS})});
				continue;
			}
			lck.lock();
		}
	}
	else
	{
		while ((implicationsSeen < basis.size()) && (!basisUpdate))
		{
			UpdateImplicationTries++;
			boost::dynamic_bitset<unsigned long> A = basis[implicationsSeen].lhs;
			boost::dynamic_bitset<unsigned long> B = basis[implicationsSeen].rhs;
			int curIndex = implicationsSeen;
			implicationsSeen++;
			boost::dynamic_bitset<unsigned long> C = A & counterExampleBS;
			lck.unlock();
			aEqualToCCount++;

			if (A != C)
			{
				aEqualToCCount--;
				auto durBegin = chrono::high_resolution_clock::now();
				boost::dynamic_bitset<unsigned long> cC = contextClosureBS(C);
				auto durEnd = chrono::high_resolution_clock::now();
				threadContextClosureTime += (chrono::duration_cast<chrono::microseconds>(durEnd - durBegin)).count();

				if (C == cC)
				{
					lck.lock();
					continue;
				}

				lck.lock();

				if (!basisUpdate)
				{
					basisUpdate = true;
					indexOfUpdatedImplication = curIndex;
					updatedImplication.lhs = C;
					updatedImplication.rhs = B;
				}

				else if (basisUpdate && (curIndex < indexOfUpdatedImplication))
				{
					indexOfUpdatedImplication = curIndex;
					updatedImplication.lhs = C;
					updatedImplication.rhs = B;
				}

				continue;
			}

			lck.lock();
		}
	}

	if (threadContextClosureTime > thisIterMaxContextClosureTime)
		thisIterMaxContextClosureTime = threadContextClosureTime;

	lck.unlock();
}

vector<implication> BSBasisToVectorBasis(vector<implicationBS> ansBS)
{
	vector<implication> ans;

	for (int i = 0; i < ansBS.size(); i++)
	{
		ans.push_back(implication{attrBSToAttrVector(ansBS[i].lhs), attrBSToAttrVector(ansBS[i].rhs)});
	}

	return ans;
}

void setNumThreads()
{
	double temp = (prevThreads * prevIterTime) / threadOverheadTime;
	temp -= (prevThreads * prevThreads);

	if (temp < 0)
	{
		numThreads = 1;
		return;
	}

	temp = sqrt(temp);
	numThreads = max((int)temp, 1);
	numThreads = min((int)numThreads, maxThreads);
	// cout << maxThreads <<","<< numThreads << endl ;
}

vector<implication> generateImplicationBasis(ThreadPool &threadPool)
{
	vector<implicationBS> ansBS;
	double prevIterTime1 = 0, prevIterTime2 = 0;
	double prevThreads1 = 1, prevThreads2 = 1;

	while (true)
	{
		auto start = chrono::high_resolution_clock::now();
		gCounter++;
		totTries = 0;
		// cout << "Going to get counter example. (Iteration Number: " << gCounter << " )" << endl;
		getLoopCount();
		// cout << "Max number of tries for this iteration: " << maxTries << "\n";
		globalFlag = true;
		counterExampleBS.clear();
		thisIterMaxContextClosureTime = 0;
		thisIterMaxImplicationClosureTime = 0;

		// if (!potentialCounterExamplesBS.empty())
		// {
		// 	tryPotentialCounterExamples(ansBS);

		// 	if(!globalFlag)
		// 		singletonCounterexamples++;

		// 	gCounter = 0;
		// }

		if (globalFlag)
		{
			prevThreads = prevThreads1;
			prevIterTime = prevIterTime1;
			setNumThreads();
			vector<std::future<void>> taskVector;

			for (int i = 1; i < numThreads; i++)
			{
				taskVector.emplace_back(threadPool.enqueue(getCounterExample, ref(ansBS), i));
			}
			//
			//This is important. If we don't write the next statement,
			//the main thread will simply keep waiting without doing anything.
			//This initially caused quite a bit of confusion, as a program without multi-threading was running faster
			//due to the main thread sitting idle.
			//
			getCounterExample(ansBS, 0);

			for (int i = 0; i < taskVector.size(); i++)
			{
				taskVector[i].get();
			}
		}

		updownTime += thisIterMaxContextClosureTime;
		totalClosureTime += thisIterMaxImplicationClosureTime;

		if (globalFlag && bothCounterExamples)
		{
			bothCounterExamples = false;
			frequentCounterExamples = false;
			gCounter = max(0, gCounter - 1);
			continue;
		}

		sumTotTries += totTries;
		if (globalFlag)
			break;

		boost::dynamic_bitset<unsigned long> X = counterExampleBS;
		//printVector(X);
		totCounterExamples++;
		// cout << "Got counter example" << endl;
		// cout << "Counterexample found after " << totTries << " tries\n";
		vector<int> counterExampleFound = attrBSToAttrVector(X);
		if (isPositiveCounterExample)
		{
			countPositiveCounterExample++;
			//	cout << "Got Positive CS  "; printVector(counterExampleFound); cout << "\n";
		}
		else
		{
			countNegativeCounterExample++;
			//	cout << "Got Negative CS  "; printVector(counterExampleFound); cout << "\n";
		}
		auto end = std::chrono::high_resolution_clock::now();
		auto duration = chrono::duration_cast<chrono::microseconds>(end - start);
		prevThreads1 = numThreads;
		prevIterTime1 = duration.count();
		// cout << duration.count() << ",";
		totalTime += duration.count();
		bool found = false;
		start = chrono::high_resolution_clock::now();
		basisUpdate = false;
		implicationsSeen = 0;
		thisIterMaxContextClosureTime = 0;

		//The algorithm implemented as-is.
		prevThreads = prevThreads2;
		prevIterTime = prevIterTime2;
		setNumThreads();

		vector<std::future<void>> taskVector;
		updatedImplications.clear();
		UpdateImplicationTries = 0;

		for (int i = 1; i < numThreads; i++)
			taskVector.emplace_back(threadPool.enqueue(tryToUpdateImplicationBasis, ref(ansBS)));

		tryToUpdateImplicationBasis(ansBS);

		for (int i = 0; i < taskVector.size(); i++)
		{
			taskVector[i].get();
		}

		updownTime += thisIterMaxContextClosureTime;
		// cout << UpdateImplicationTries << " iterations in tryToUpdateImplicationBasis\n";

		if (isPositiveCounterExample)
		{
			for (auto &updateImp : updatedImplications)

			{
				vector<int> initial_lhs = attrBSToAttrVector(ansBS[updateImp.first].lhs),
							initial_rhs = attrBSToAttrVector(ansBS[updateImp.first].rhs);
				// cout<<"\nPrevious implication at index "<<updateImp.first<<" was: ";printVector(initial_lhs);cout<<" ==> ";printVector(initial_rhs);cout<<"\n";
				ansBS[updateImp.first] = updateImp.second;

				vector<int> new_lhs = attrBSToAttrVector(ansBS[updateImp.first].lhs),
							new_rhs = attrBSToAttrVector(ansBS[updateImp.first].rhs);
				// cout<<"Now implication is :";printVector(initial_lhs);cout<<" ==> ";printVector(initial_rhs);cout<<"\n\n";
			}
			cout << endl;
		}
		else
		{
			if (!basisUpdate)
			{
				// ansBS.push_back(implicationBS{X, contextClosureBS(X)});
				boost::dynamic_bitset<unsigned long> allattribute(attrInp.size());
				allattribute.set();
				allattribute[0] = false;
				ansBS.push_back(implicationBS{X, allattribute});

				// only for debugging
				vector<int> vectorX = attrBSToAttrVector(X), vectorM = attrBSToAttrVector(allattribute);
				// cout << "Adding X -> M as : "; printVector(vectorX); cout << " ==> "; printVector(vectorM); cout << "\n\n";
			}
			else
			{
				vector<int> initialLHS = attrBSToAttrVector(ansBS[indexOfUpdatedImplication].lhs),
							initialRHS = attrBSToAttrVector(ansBS[indexOfUpdatedImplication].rhs),
							newLHS = attrBSToAttrVector(updatedImplication.lhs),
							newRHS = attrBSToAttrVector(updatedImplication.rhs);
				// cout << "Initial Implication: "; printVector(initialLHS); cout << " ==> "; printVector(initialRHS); cout << "\n";
				// cout << "Updated Implication: "; printVector(newLHS); cout << " ==> "; printVector(newRHS); cout << "\n\n";
				ansBS[indexOfUpdatedImplication] = updatedImplication;
			}
		}

		end = std::chrono::high_resolution_clock::now();
		totalExecTime2 += (chrono::duration_cast<chrono::microseconds>(end - start)).count();
		duration = chrono::duration_cast<chrono::microseconds>(end - start);
		prevThreads2 = numThreads;
		prevIterTime2 = duration.count();
		// cout << duration.count() << "\n";
	}

	ansBasisBS = ansBS;
	return BSBasisToVectorBasis(ansBS);
}
vector<double> confidenceOfImplicationBasis;

vector<int> supp_imp;
vector<int> supp_prem;

void FindConfidenceOfImplications()
{

	for (int i = 0; i < ansBasisBS.size(); i++)
	{
		int support_premsis = 0;
		int support_implication = 0;
		for (int j = 0; j < objInpBS.size(); j++)
		{

			if (ansBasisBS[i].lhs.is_subset_of(objInpBS[j]))
			{
				support_premsis++;
			}

			if (ansBasisBS[i].lhs.is_subset_of(objInpBS[j]) && ansBasisBS[i].rhs.is_subset_of(objInpBS[j]))
			{
				support_implication++;
			}
		}
		supp_imp.push_back(support_implication);
		supp_prem.push_back(support_premsis);
		confidenceOfImplicationBasis.push_back((double)support_implication / support_premsis);
	}
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
	for (int i = 1; i < attrInp.size(); i++)
	{
		vector<int> cVec = {i};
		potentialCounterExamplesBS.push_back(attrVectorToAttrBS(cVec));
	}
}

void initializeObjInpBS()
{
	objInpBS.resize(objInp.size());

	for (int i = 0; i < objInp.size(); i++)
	{
		objInpBS[i] = attrVectorToAttrBS(objInp[i]);
	}
}

bool isLectGreater(boost::dynamic_bitset<unsigned long> &closedSet, int lectInd)
{
	for (int i = 0; i <= lectInd; i++)
		if (closedSet[frequencyOrderedAttributes[i]])
			return true;

	return false;
}

boost::dynamic_bitset<unsigned long> nextContextClosure(boost::dynamic_bitset<unsigned long> A, boost::dynamic_bitset<unsigned long> finalClosedSet)
{
	int nAttr = attrInp.size() - 1;

	for (int i = nAttr; i > 0; i--)
	{
		if (A[frequencyOrderedAttributes[i]])
			A[frequencyOrderedAttributes[i]] = false;
		else
		{
			boost::dynamic_bitset<unsigned long> B, temp = A;
			temp[frequencyOrderedAttributes[i]] = true;
			B = contextClosureBS(temp);

			bool flag = true;

			for (int j = 1; j < i; j++)
			{
				if (B[frequencyOrderedAttributes[j]] & (!A[frequencyOrderedAttributes[j]]))
				{
					flag = false;
					break;
				}
			}

			if (flag)
				return B;
		}
	}

	return finalClosedSet;
}

int allContextClosures()
{
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

	while (currentClosedSet != finalClosedSet)
	{
		currentClosedSet = nextContextClosure(currentClosedSet, finalClosedSet);
		totalClosedSets++;
		auto timeNow = chrono::high_resolution_clock::now();
		double duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timePrev)).count();

		if (duration > 60000000)
		{
			// cout <<"Total Context closures till now: "<< totalClosedSets << endl;
			timePrev = timeNow;
		}

		if ((!lectDone) && isLectGreater(currentClosedSet, lectInd))
		{
			lectLessClosures = totalClosedSets;
			lectDone = true;
		}

		duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timeStart)).count();

		if (lectDone && (duration > 6000000))
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

	for (int i = nAttr; i > 0; i--)
	{
		if (A[frequencyOrderedAttributes[i]])
			A[frequencyOrderedAttributes[i]] = false;
		else
		{
			boost::dynamic_bitset<unsigned long> B, temp = A;
			temp[frequencyOrderedAttributes[i]] = true;
			B = closureBS(ansBasisBS, temp);

			bool flag = true;

			for (int j = 1; j < i; j++)
			{
				if (B[frequencyOrderedAttributes[j]] & (!A[frequencyOrderedAttributes[j]]))
				{
					flag = false;
					break;
				}
			}

			if (flag)
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
	int lectInd = max(1, ((3 * nattr) / 4)), lectLessClosures;
	bool lectDone = false;
	auto timeStart = chrono::high_resolution_clock::now();
	auto timePrev = chrono::high_resolution_clock::now();

	while (currentClosedSet != finalClosedSet)
	{
		currentClosedSet = nextImplicationClosure(currentClosedSet, finalClosedSet);
		totalClosedSets++;

		auto timeNow = chrono::high_resolution_clock::now();
		double duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timePrev)).count();

		if (duration > 60000000)
		{
			// cout <<"Total Implication closures till now: "<< totalClosedSets << endl;
			timePrev = timeNow;
		}

		if ((!lectDone) && isLectGreater(currentClosedSet, lectInd))
		{
			lectLessClosures = totalClosedSets;
			lectDone = true;
		}

		duration = (chrono::duration_cast<chrono::microseconds>(timeNow - timeStart)).count();

		if (lectDone && (duration > 6000000))
		{
			// cout <<"Lectically less Implication Closures:"<< lectLessClosures << endl;
			return lectLessClosures;
		}
	}

	// cout <<"Lectically less Implication Closures:"<< lectLessClosures << endl;
	return lectLessClosures;
}

void getSupportOfImplicationsFrequent()
{
	vector<long long> supports;

	for (int i = 0; i < ansBasisBS.size(); i++)
	{
		long long support = 0;

		for (int j = 0; j < objInpBS.size(); j++)
		{
			if (ansBasisBS[i].lhs.is_subset_of(objInpBS[j]))
				support++;
		}

		supports.push_back(support);
	}

	sort(supports.rbegin(), supports.rend());
	double meanSupport = accumulate(supports.begin(), supports.end(), (double)0);
	meanSupport /= supports.size();
	double p10, p50, p90, p95;
	p10 = supports[0.1 * supports.size()];
	p50 = supports[0.5 * supports.size()];
	p90 = supports[0.9 * supports.size()];
	p95 = supports[0.95 * supports.size()];
	cout << 100 * meanSupport / objInpBS.size() << ";";
	cout << 100 * p10 / objInpBS.size() << ";";
	cout << 100 * p50 / objInpBS.size() << ";";
	cout << 100 * p90 / objInpBS.size() << ";";
	cout << 100 * p95 / objInpBS.size() << ";";
	return;
}

void getSupportOfImplicationsArea()
{
	vector<long long> supports;

	for (int i = 0; i < ansBasisBS.size(); i++)
	{
		long long support = 0;

		for (int j = 0; j < objInpBS.size(); j++)
		{
			if (ansBasisBS[i].lhs.is_subset_of(objInpBS[j]))
				support++;
		}

		supports.push_back(support * ansBasisBS[i].lhs.count());
	}

	sort(supports.rbegin(), supports.rend());
	double meanSupport = accumulate(supports.begin(), supports.end(), (double)0);
	meanSupport /= supports.size();
	double p10, p50, p90, p95;
	p10 = supports[0.1 * supports.size()];
	p50 = supports[0.5 * supports.size()];
	p90 = supports[0.9 * supports.size()];
	p95 = supports[0.95 * supports.size()];
	cout << meanSupport << ";";
	cout << p10 << ";";
	cout << p50 << ";";
	cout << p90 << ";";
	cout << p95 << ";";
	return;
}

void getSupportOfImplicationsSquared()
{
	vector<long long> supports;

	for (int i = 0; i < ansBasisBS.size(); i++)
	{
		long long support = 0;

		for (int j = 0; j < objInpBS.size(); j++)
		{
			if (ansBasisBS[i].lhs.is_subset_of(objInpBS[j]))
				support++;
		}

		supports.push_back(support * support);
	}

	sort(supports.rbegin(), supports.rend());
	double meanSupport = accumulate(supports.begin(), supports.end(), (double)0);
	meanSupport /= supports.size();
	double p10, p50, p90, p95;
	p10 = supports[0.1 * supports.size()];
	p50 = supports[0.5 * supports.size()];
	p90 = supports[0.9 * supports.size()];
	p95 = supports[0.95 * supports.size()];
	double numObjSq = objInpBS.size();
	numObjSq *= numObjSq;
	cout << 100 * meanSupport / numObjSq << ";";
	cout << 100 * p10 / numObjSq << ";";
	cout << 100 * p50 / numObjSq << ";";
	cout << 100 * p90 / numObjSq << ";";
	cout << 100 * p95 / numObjSq << ";";
	return;
}

void initFrequencyOrderedAttributes()
{
	vector<int> freqAttr(attrInp.size(), 0);

	for (int i = 0; i < objInp.size(); i++)
	{
		for (int j = 0; j < objInp[i].size(); j++)
			freqAttr[objInp[i][j]]++;
	}

	vector<pair<int, int>> freqPairs;

	for (int i = 1; i < attrInp.size(); i++)
	{
		freqPairs.push_back({freqAttr[i], i});
	}

	sort(freqPairs.begin(), freqPairs.end());
	frequencyOrderedAttributes.push_back(0);

	for (int i = 0; i < freqPairs.size(); i++)
		frequencyOrderedAttributes.push_back(freqPairs[i].second);
}

int NoOFExactRules = 0;
int NoOfRulesConfHighThanPoint9 = 0;

void CountExactRules()
{

	for (int i = 0; i < confidenceOfImplicationBasis.size(); i++)
	{
		if (confidenceOfImplicationBasis[i] == 1)
		{
			NoOFExactRules++;
			NoOfRulesConfHighThanPoint9++;
		}
		else if (confidenceOfImplicationBasis[i] > 0.9)
		{
			NoOfRulesConfHighThanPoint9++;
		}
	}
}

int main(int argc, char **argv)
{
	auto startTime = chrono::high_resolution_clock::now();
	srand(time(NULL));
	//cout <<"argc = "<< argc << "\n";

	if (argc < 8)
	{
		printUsageAndExit();
	}

	readFormalContext1(argv[1]);
	initializeObjInpBS();
	initFrequencyOrderedAttributes();
	epsilon = atof(argv[2]);
	del = atof(argv[3]);
	if (string(argv[4]) == string("strong"))
		epsilonStrong = true;

	if (string(argv[5]) != string("uniform"))
	{
		frequentCounterExamples = true;
		string temp = argv[5];

		if (temp == string("area"))
			counterexampleType = 2;
		if (temp == string("squared"))
			counterexampleType = 3;
		if (temp == string("discriminativity"))
		{
			counterexampleType = 4;
			readLabels(argv[8]);
		}
		if (temp == "binomial")
			counterexampleType = 5;
	}

	if (string(argv[5]) == string("both"))
		bothCounterExamples = true;

	maxThreads = atoi(argv[6]);
	numThreads = 1;
	if (string(argv[7]) == string("support"))
		implicationSupport = true;

	ThreadPool threadPool(maxThreads - 1);
	fillPotentialCounterExamples();
	initializeRandSetGen();
	vector<implication> ans = generateImplicationBasis(threadPool);
	FindConfidenceOfImplications();

	CountExactRules();
	// cout << totalTime << "\n";

	auto endTime = chrono::high_resolution_clock::now();
	double TotalExecTime = 0;
	TotalExecTime += (chrono::duration_cast<chrono::microseconds>(endTime - startTime)).count();

	startTime = chrono::high_resolution_clock::now();

	double qf = (double)allContextClosures() / allImplicationClosures();

	endTime = chrono::high_resolution_clock::now();

	double Time_qf = (chrono::duration_cast<chrono::microseconds>(endTime - startTime)).count();

	cout << "\n";
	for (int i = 2; i < 7; i++)
		cout << argv[i] << ", ";

	cout << TIMEPRINT(TotalExecTime) << ",";
	cout << TIMEPRINT(totalTime) << ",";
	cout << TIMEPRINT(totalExecTime2) << ",";
	cout << TIMEPRINT(totalClosureTime) << ",";
	cout << TIMEPRINT(updownTime) << ",";
	cout << totClosureComputations << ",";
	cout << totUpDownComputes << ", ";
	cout << "No. of implications : " << ans.size() << ", ";
	cout << "Total Positive Counterexamples: " << countPositiveCounterExample << ", ";
	cout << "Total Negative Counterexamples: " << countNegativeCounterExample << ", ";
	cout << "Total Counterexamples: " << totCounterExamples << ",";
	cout << sumTotTries << ",";
	cout << aEqualToCCount << ",";
	cout << emptySetClosureComputes << ",";
	cout << singletonCounterexamples << ";" << flush;
	//cout << allContextClosures() << "," << flush;
	if (implicationSupport)
	{
		getSupportOfImplicationsFrequent();
		getSupportOfImplicationsArea();
		getSupportOfImplicationsSquared();
	}

	// cout << allImplicationClosures() << endl;

	cout << endl;

	for (int i = 0; i < ans.size(); i++)
	{
		// //cout << "Implication\n";

		printVector(ans[i].lhs);
		cout << "==> ";
		printVector(ans[i].rhs);
		cout << "confidence " << confidenceOfImplicationBasis[i] << "\n";
		cout << "LHSsupport " << supp_prem[i] << "\n";
		cout << "ImplicationSupport: " << supp_imp[i] << "\n";
	}

	cout << TIMEPRINT(TotalExecTime) << ",";
	cout << "No of Iterations: " << gCounter << endl;
	cout << "No. of implications : " << ans.size() << "\n";
	cout << "Total Positive Counterexamples: " << countPositiveCounterExample << "\n";
	cout << "Total Negative Counterexamples: " << countNegativeCounterExample << "\n";
	cout << "Total Counterexamples: " << totCounterExamples << "\n";
	cout << "No of Exact Association Rules: " << NoOFExactRules << endl;
	cout << "No of Rules With Confidence higher than 0.9 : " << NoOfRulesConfHighThanPoint9 << endl;
	cout << "Qualtiy factor : " << qf << "\n";
	cout << "Time to calculate quality factor is " << TIMEPRINT(Time_qf) << endl;
	return 0;
}
