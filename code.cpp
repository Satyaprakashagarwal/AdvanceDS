#include <bits/stdc++.h>
using namespace std;

/**
 * AdvancedDS: a feature-rich container
 * Core structure: Doubly Linked List (order), plus auxiliary indices.
 *
 * Operations (typical cost):
 *  - pushBack / pushFront / popBack / popFront / front / back / top : O(1)
 *  - search / contains / getFrequency / size / empty : O(1) average
 *  - deleteVal(x) / update(old->new) : O(1) avg for locating + O(log n) to fix min/max/median/mode
 *  - getMin / getMax : O(1) (multiset begin/rbegin)
 *  - getMedian : O(1) (two multisets)
 *  - getMode : O(1)
 *  - getRandom : O(1)
 *  - traverse / getKth / reverse / rotate(k) : O(n)
 *  - sortAscending / sortDescending / nextPermutation / prevPermutation : O(n log n) or O(n); then rebuild indices
 *  - uniqueElements / removeDuplicates : O(n)
 */

class AdvancedDS {
    struct Node {
        int val;
        Node *prev, *next;
        Node(int v): val(v), prev(nullptr), next(nullptr) {}
    };

    // Doubly-linked list to maintain order
    Node *head = nullptr, *tail = nullptr;
    size_t sz = 0;

    // Value -> set of node pointers (supports duplicates, O(1) erase by pointer)
    unordered_map<int, unordered_set<Node*>> locs;

    // Frequency + mode tracking
    unordered_map<int,int> freq;
    int modeVal = 0;
    int modeCnt = 0;

    // Min/Max (all values)
    multiset<int> allVals;

    // Median maintenance: lower = max half, upper = min half
    multiset<int> lower, upper; // invariants: |lower| >= |upper| and |lower|-|upper|<=1

    // Random support: pool of node pointers + index map (swap-remove)
    vector<Node*> pool;
    unordered_map<Node*, size_t> poolPos;
    mt19937 rng{random_device{}()};

    // ---- Helpers ----
    void attachBack(Node* node) {
        if (!tail) head = tail = node;
        else {
            tail->next = node;
            node->prev = tail;
            tail = node;
        }
    }
    void attachFront(Node* node) {
        if (!head) head = tail = node;
        else {
            node->next = head;
            head->prev = node;
            head = node;
        }
    }
    void detach(Node* node) {
        if (node->prev) node->prev->next = node->next; else head = node->next;
        if (node->next) node->next->prev = node->prev; else tail = node->prev;
        node->prev = node->next = nullptr;
    }

    void poolAdd(Node* node) {
        poolPos[node] = pool.size();
        pool.push_back(node);
    }
    void poolRemove(Node* node) {
        auto it = poolPos.find(node);
        if (it == poolPos.end()) return;
        size_t idx = it->second;
        size_t last = pool.size() - 1;
        if (idx != last) {
            pool[idx] = pool[last];
            poolPos[pool[idx]] = idx;
        }
        pool.pop_back();
        poolPos.erase(node);
    }

    void modeInc(int x) {
        int f = ++freq[x];
        if (f > modeCnt || (f == modeCnt && x < modeVal)) {
            modeCnt = f;
            modeVal = x;
        }
    }
    void modeDec(int x) {
        auto it = freq.find(x);
        if (it == freq.end()) return;
        it->second--;
        if (it->second == 0) freq.erase(it);
        // Recompute mode if needed (rare path)
        if (x == modeVal && (freq.count(x) == 0 || freq[x] < modeCnt)) {
            modeCnt = 0;
            for (auto &p : freq) {
                if (p.second > modeCnt || (p.second == modeCnt && p.first < modeVal)) {
                    modeCnt = p.second;
                    modeVal = p.first;
                }
            }
        }
    }

    void medianAdd(int x) {
        if (lower.empty() || x <= *lower.rbegin()) lower.insert(x);
        else upper.insert(x);
        rebalanceMedian();
    }
    void medianRemove(int x) {
        // erase one instance from the correct multiset
        if (!lower.empty() && x <= *lower.rbegin()) {
            auto it = lower.find(x);
            if (it != lower.end()) lower.erase(it);
            else {
                auto iu = upper.find(x);
                if (iu != upper.end()) upper.erase(iu);
            }
        } else {
            auto iu = upper.find(x);
            if (iu != upper.end()) upper.erase(iu);
            else {
                auto il = lower.find(x);
                if (il != lower.end()) lower.erase(il);
            }
        }
        rebalanceMedian();
    }
    void rebalanceMedian() {
        if (lower.size() > upper.size() + 1) {
            auto it = prev(lower.end());
            upper.insert(*it);
            lower.erase(it);
        } else if (upper.size() > lower.size()) {
            auto it = upper.begin();
            lower.insert(*it);
            upper.erase(it);
        }
    }

    void addValueStructures(int x, Node* node) {
        locs[x].insert(node);
        modeInc(x);
        allVals.insert(x);
        medianAdd(x);
        poolAdd(node);
        sz++;
    }
    void removeValueStructures(int x, Node* node) {
        // locs
        auto lit = locs.find(x);
        if (lit != locs.end()) {
            lit->second.erase(node);
            if (lit->second.empty()) locs.erase(lit);
        }
        // freq/mode
        modeDec(x);
        // min/max
        auto it = allVals.find(x);
        if (it != allVals.end()) allVals.erase(it);
        // median
        medianRemove(x);
        // random pool
        poolRemove(node);
        sz--;
    }

    // Rebuild all auxiliary structures from the current linked list
    void rebuildAll() {
        locs.clear();
        freq.clear();
        allVals.clear();
        lower.clear();
        upper.clear();
        pool.clear();
        poolPos.clear();
        modeCnt = 0;
        modeVal = 0;
        // traverse and add
        for (Node* cur = head; cur; cur = cur->next) {
            addValueStructures(cur->val, cur);
        }
    }

public:
    ~AdvancedDS() {
        clear();
    }

    // ---------- Basic info ----------
    bool empty() const { return sz == 0; }
    size_t size() const { return sz; }

    // ---------- Push/Pop / Front/Back ----------
    void pushBack(int x) {
        Node* node = new Node(x);
        attachBack(node);
        addValueStructures(x, node);
    }
    void pushFront(int x) {
        Node* node = new Node(x);
        attachFront(node);
        addValueStructures(x, node);
    }
    void popBack() {
        if (!tail) return;
        Node* node = tail;
        int x = node->val;
        detach(node);
        removeValueStructures(x, node);
        delete node;
    }
    void popFront() {
        if (!head) return;
        Node* node = head;
        int x = node->val;
        detach(node);
        removeValueStructures(x, node);
        delete node;
    }
    int front() const { return head ? head->val : INT_MIN; }
    int back()  const { return tail ? tail->val : INT_MIN; }
    int top()   const { return back(); } // alias

    // ---------- Search / Frequency ----------
    bool contains(int x) const { return freq.count(x) > 0; }
    int getFrequency(int x) const {
        auto it = freq.find(x);
        return (it == freq.end()) ? 0 : it->second;
    }

    // ---------- Min/Max/Median/Mode ----------
    int getMin() const { return allVals.empty() ? INT_MAX : *allVals.begin(); }
    int getMax() const { return allVals.empty() ? INT_MIN : *allVals.rbegin(); }
    double getMedian() const {
        if (sz == 0) return numeric_limits<double>::quiet_NaN();
        if (lower.size() > upper.size()) return *lower.rbegin();
        return ( (double)*lower.rbegin() + (double)*upper.begin() ) / 2.0;
        // If you prefer integer median when even, return *lower.rbegin()
    }
    int getMode() const {
        return (modeCnt == 0) ? INT_MIN : modeVal;
    }

    // ---------- Delete / Update ----------
    // delete one occurrence of x (if exists)
    bool deleteVal(int x) {
        auto it = locs.find(x);
        if (it == locs.end() || it->second.empty()) return false;
        Node* node = *it->second.begin();
        detach(node);
        removeValueStructures(x, node);
        delete node;
        return true;
    }

    // update one occurrence of oldVal to newVal
    bool update(int oldVal, int newVal) {
        auto it = locs.find(oldVal);
        if (it == locs.end() || it->second.empty()) return false;
        Node* node = *it->second.begin();
        // remove old tracking
        // careful: we keep the node in place; adjust all structures
        // remove old from all tracking
        {
            // locs
            it->second.erase(node);
            if (it->second.empty()) locs.erase(it);
            // freq/mode
            modeDec(oldVal);
            // min/max
            auto a = allVals.find(oldVal);
            if (a != allVals.end()) allVals.erase(a);
            // median
            medianRemove(oldVal);
        }
        // set new value
        node->val = newVal;
        // add new tracking
        addValueStructures(newVal, node);
        return true;
    }

    // ---------- Traversal / Kth ----------
    void traverse(ostream& os = cout) const {
        for (Node* cur = head; cur; cur = cur->next) os << cur->val << ' ';
        os << '\n';
    }
    // O(n) kth (0-indexed)
    bool getKth(size_t k, int &out) const {
        if (k >= sz) return false;
        Node* cur = head;
        while (k--) cur = cur->next;
        out = cur->val;
        return true;
    }

    // ---------- Reverse / Rotate ----------
    // Reverse in O(n)
    void reverse() {
        Node* cur = head;
        Node* prevNode = nullptr;
        tail = head;
        while (cur) {
            Node* nxt = cur->next;
            cur->next = prevNode;
            cur->prev = nxt;
            prevNode = cur;
            cur = nxt;
        }
        head = prevNode;
        // values unchanged; auxiliary structures unaffected
    }

    // Rotate right by k (last k become first). O(n) to locate split.
    void rotate(size_t k) {
        if (sz == 0) return;
        k %= sz;
        if (k == 0) return;
        // newTail at position sz-k-1, newHead at sz-k
        size_t steps = sz - k - 1;
        Node* newTail = head;
        while (steps--) newTail = newTail->next;
        Node* newHead = newTail->next;

        // reconnect
        newTail->next = nullptr;
        newHead->prev = nullptr;
        tail->next = head;
        head->prev = tail;

        head = newHead;
        tail = newTail;
    }

    // ---------- Random ----------
    int getRandom() {
        if (pool.empty()) return INT_MIN;
        uniform_int_distribution<size_t> dist(0, pool.size()-1);
        Node* node = pool[dist(rng)];
        return node->val;
    }

    // ---------- Unique / Remove Duplicates ----------
    vector<int> uniqueElements() const {
        vector<int> keys;
        keys.reserve(freq.size());
        for (auto &p : freq) keys.push_back(p.first);
        return keys;
    }

    // keep first occurrence order, remove later duplicates (O(n))
    void removeDuplicates() {
        unordered_set<int> seen;
        for (Node* cur = head; cur; ) {
            Node* nxt = cur->next;
            if (seen.count(cur->val)) {
                // remove this node
                int x = cur->val;
                detach(cur);
                removeValueStructures(x, cur);
                delete cur;
            } else {
                seen.insert(cur->val);
            }
            cur = nxt;
        }
    }

    // ---------- Sorting / Permutations ----------
    void sortAscending() {
        if (sz <= 1) return;
        vector<int> a; a.reserve(sz);
        for (Node* cur = head; cur; cur = cur->next) a.push_back(cur->val);
        sort(a.begin(), a.end());
        // write back
        Node* cur = head; size_t i = 0;
        while (cur) { cur->val = a[i++]; cur = cur->next; }
        rebuildAll();
    }
    void sortDescending() {
        if (sz <= 1) return;
        vector<int> a; a.reserve(sz);
        for (Node* cur = head; cur; cur = cur->next) a.push_back(cur->val);
        sort(a.rbegin(), a.rend());
        Node* cur = head; size_t i = 0;
        while (cur) { cur->val = a[i++]; cur = cur->next; }
        rebuildAll();
    }

    bool nextPermutation() {
        if (sz <= 1) return false;
        vector<int> a; a.reserve(sz);
        for (Node* cur = head; cur; cur = cur->next) a.push_back(cur->val);
        bool ok = std::next_permutation(a.begin(), a.end());
        Node* cur = head; size_t i = 0;
        while (cur) { cur->val = a[i++]; cur = cur->next; }
        rebuildAll();
        return ok;
    }
    bool prevPermutation() {
        if (sz <= 1) return false;
        vector<int> a; a.reserve(sz);
        for (Node* cur = head; cur; cur = cur->next) a.push_back(cur->val);
        bool ok = std::prev_permutation(a.begin(), a.end());
        Node* cur = head; size_t i = 0;
        while (cur) { cur->val = a[i++]; cur = cur->next; }
        rebuildAll();
        return ok;
    }

    // ---------- Merge / Split / Clear ----------
    // Append all from other to this (other becomes empty). O(n_other)
    void merge(AdvancedDS &other) {
        if (other.sz == 0) return;
        if (sz == 0) {
            head = other.head;
            tail = other.tail;
        } else {
            tail->next = other.head;
            other.head->prev = tail;
            tail = other.tail;
        }
        sz += other.sz;
        // integrate aux structures efficiently by traversing other's list:
        for (Node* cur = other.head; cur; cur = cur->next) {
            locs[cur->val].insert(cur);
            modeInc(cur->val);
            allVals.insert(cur->val);
            medianAdd(cur->val);
            poolAdd(cur);
        }
        // clear "other"
        other.head = other.tail = nullptr;
        other.sz = 0;
        other.locs.clear();
        other.freq.clear();
        other.allVals.clear();
        other.lower.clear();
        other.upper.clear();
        other.pool.clear();
        other.poolPos.clear();
        other.modeCnt = 0;
        other.modeVal = 0;
        rebalanceMedian();
    }

    // Split after k nodes (left keeps first k, right gets the rest)
    AdvancedDS split(size_t k) {
        AdvancedDS right;
        if (k >= sz) return right;
        if (k == 0) {
            right.merge(*this);
            return right;
        }
        Node* cur = head;
        size_t cnt = k-1;
        while (cnt--) cur = cur->next;
        Node* newHead = cur->next;

        // detach
        cur->next = nullptr;
        if (newHead) newHead->prev = nullptr;

        // right takes newHead..tail
        right.head = newHead;
        right.tail = tail;

        // this keeps head..cur
        tail = cur;

        // recompute both structures
        size_t oldSz = sz;
        // recompute sizes by traversal (O(n))
        sz = 0;
        for (Node* p = head; p; p = p->next) sz++;
        right.sz = 0;
        for (Node* p = right.head; p; p = p->next) right.sz++;

        // rebuild aux structures (simpler & safe)
        rebuildAll();
        right.rebuildAll();

        return right;
    }

    void clear() {
        Node* cur = head;
        while (cur) {
            Node* nxt = cur->next;
            delete cur;
            cur = nxt;
        }
        head = tail = nullptr;
        sz = 0;
        locs.clear();
        freq.clear();
        allVals.clear();
        lower.clear();
        upper.clear();
        pool.clear();
        poolPos.clear();
        modeCnt = 0;
        modeVal = 0;
    }
};

// ----------------- Example usage -----------------
/*
int main() {
    AdvancedDS ds;
    ds.pushBack(3);
    ds.pushBack(1);
    ds.pushBack(2);
    ds.pushFront(5);
    ds.traverse();                 // 5 3 1 2

    cout << "Min " << ds.getMin() << " Max " << ds.getMax() << "\n";
    cout << "Median " << ds.getMedian() << " Mode " << ds.getMode() << "\n";

    ds.sortAscending();
    ds.traverse();                 // 1 2 3 5

    ds.nextPermutation();
    ds.traverse();                 // 1 2 5 3

    cout << "Random: " << ds.getRandom() << "\n";

    ds.deleteVal(2);
    ds.traverse();                 // 1 5 3

    ds.update(5, 7);
    ds.traverse();                 // 1 7 3

    //ds.rotate(1);
    //ds.traverse();                 // 3 1 7

    auto uniques = ds.uniqueElements();
    cout << "Unique keys: ";
    for (int x : uniques) cout << x << ' ';
    cout << "\n";

    AdvancedDS right = ds.split(2);
    cout << "Left: "; ds.traverse();      // 3 1
    cout << "Right: "; right.traverse();  // 7
}
*/
