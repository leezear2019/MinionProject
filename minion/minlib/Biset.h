//
// Created by lee on 2019/11/11.
//

#ifndef MINIONPROJECT_BISET_H
#define MINIONPROJECT_BISET_H


#include <vector>

namespace CTRL {

    class Biset;

    class Iterator {
    public:
        friend class Biset;

        // 取值
        int Value() const noexcept;

        int Index() const noexcept;

        bool IsFormerBegin() const noexcept;

        bool IsLatterBegin() const noexcept;

        bool IsFormerEnd() const noexcept;

        bool IsLatterEnd() const noexcept;

        bool BeforeFormerBegin() const noexcept;

        bool BeforeLatterBegin() const noexcept;

        bool AfterFormerEnd() const noexcept;

        bool AfterLatterEnd() const noexcept;

        void operator++() noexcept;

        void operator--() noexcept;

        void MoveToLatterAndGoPrevious() noexcept;

        void MoveToLatter() noexcept;

        void MoveToFormer() noexcept;

        void MoveToFormerAndGoNext() noexcept;

    private:
        Iterator(Biset *s, int i);

        void previous() noexcept;

        void next() noexcept;

        int i_;
        int length_;
        Biset *s_;
    };


    // 二部集合，集合中元素不是属于上一类就是属于下一类，其中上一个集合称为former,后一个集合称为latter
    // 采用稀疏集的数据结构
    class Biset {
    public:
        friend class Iterator;

        Biset();

        // 初始化时所有的元素都属于former集合
        Biset(int size);

        void Resize(int size);

        // 标记一个状态
        void Mark();

        // 回到设定的状态
        void BackToMark();

        bool BelongToFront(int a) const noexcept;

        bool BelongToLatter(int a) const noexcept;

        void MoveElementToLatter(int a) noexcept;

        void MoveElementToFormer(int a) noexcept;

        int FormerSize() const noexcept;

        int LatterSize() const noexcept;

        void MoveAllToFormer() noexcept;

        void MoveAllToLatter() noexcept;

        Iterator FormerBegin() noexcept;

        Iterator LatterBegin() noexcept;

        Iterator FormerEnd() noexcept;

        Iterator LatterEnd() noexcept;

    private:
        inline void swap(const int i, const int j) noexcept;

        int getValue(const int i) const noexcept;

        std::vector<int> dense_;
        std::vector<int> sparse_;

        //  sep_index_用来分隔两个集合，sep_index(不含sep_index_)之前的所有元素属于former,
        //  默认都属于former
        int sep_;

        // 标记一个状态用于回溯
        int mark_;

        // 总长度
        int size_;
    };

    //////////////////////////////////////////////////////////////////////////////////////

    Biset::Biset() {

    }

    Biset::Biset(const int size) :
            size_(size) {
        sep_ = size;
        mark_ = size;
        dense_.resize(size);
        sparse_.resize(size);

        for (int i = 0; i < size_; ++i) {
            dense_[i] = i;
            sparse_[i] = i;
        }
    }

    void Biset::Resize(const int size) {
        size_ = size;
        sep_ = size;
        mark_ = size;
        dense_.reserve(size);
        sparse_.reserve(size);

        for (int i = 0; i < size_; ++i) {
            dense_[i] = i;
            sparse_[i] = i;
        }
    }


    void Biset::Mark() {
        mark_ = sep_;
    }

    void Biset::BackToMark() {
        sep_ = mark_;

    }

    bool Biset::BelongToFront(const int a) const noexcept {
        return sparse_[a] < sep_;
    }

    bool Biset::BelongToLatter(const int a) const noexcept {
        return sparse_[a] >= sep_;
    }

    void Biset::MoveElementToLatter(const int a) noexcept {
        if (BelongToFront(a)) {
            swap(sparse_[a], --sep_);
        }
    }

    void Biset::MoveElementToFormer(const int a) noexcept {
        if (BelongToLatter(a)) {
            swap(sep_++, sparse_[a]);
        }
    }

    void Biset::swap(const int i, const int j) noexcept {
        int tmp = dense_[i];
        dense_[i] = dense_[j];
        dense_[j] = tmp;

        sparse_[dense_[i]] = i;
        sparse_[dense_[j]] = j;
    }

    int Biset::getValue(const int i) const noexcept {
        return dense_[i];
    }

    int Biset::FormerSize() const noexcept {
        return sep_;
    }

    int Biset::LatterSize() const noexcept {
        return size_ - sep_;
    }

    void Biset::MoveAllToFormer() noexcept {
        sep_ = size_;
    }

    void Biset::MoveAllToLatter() noexcept {
        sep_ = 0;
    }

    Iterator Biset::LatterEnd() noexcept {
        return Iterator(this, size_);
    }

    Iterator Biset::FormerBegin() noexcept {
        return Iterator(this, 0);
    }

    Iterator Biset::LatterBegin() noexcept {
        return Iterator(this, sep_);
    }

    Iterator Biset::FormerEnd() noexcept {
        return Iterator(this, sep_ - 1);
    }

    //////////////////////////////////////////////////////////////////////////////////////

    Iterator::Iterator(Biset *s, const int i) :
            s_(s),
            i_(i),
            length_(s->size_) {}

    int Iterator::Value() const noexcept {
        return s_->getValue(i_);
    }

    int Iterator::Index() const noexcept {
        return i_;
    }

    bool Iterator::IsFormerBegin() const noexcept {
        return i_ == 0;
    }

    bool Iterator::IsLatterBegin() const noexcept {
        return i_ == s_->sep_;
    }

    bool Iterator::IsFormerEnd() const noexcept {
        return i_ == s_->sep_ - 1;
    }

    bool Iterator::IsLatterEnd() const noexcept {
        return i_ == length_ - 1;
    }

    bool Iterator::BeforeFormerBegin() const noexcept {
        return i_ < 0;
    }

    bool Iterator::BeforeLatterBegin() const noexcept {
        return i_ < s_->sep_;
    }

    bool Iterator::AfterFormerEnd() const noexcept {
        return i_ >= s_->sep_;
    }

    bool Iterator::AfterLatterEnd() const noexcept {
        return i_ >= length_;
    }

    void Iterator::operator--() noexcept {
        --i_;
    }

    void Iterator::operator++() noexcept {
        ++i_;
    }

    void Iterator::previous() noexcept {
        --i_;
    }

    void Iterator::next() noexcept {
        ++i_;
    }

    void Iterator::MoveToLatterAndGoPrevious() noexcept {
        s_->MoveElementToLatter(s_->dense_[i_]);
        previous();
    }

    void Iterator::MoveToLatter() noexcept {
        s_->MoveElementToLatter(s_->dense_[i_]);
    }

    void Iterator::MoveToFormer() noexcept {
        s_->MoveElementToFormer(s_->dense_[i_]);
    }

    void Iterator::MoveToFormerAndGoNext() noexcept {
        s_->MoveElementToFormer(s_->dense_[i_]);
        next();
    }

}


#endif //MINIONPROJECT_BISET_H
