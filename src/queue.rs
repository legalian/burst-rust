

use std::cmp::Ordering;

pub struct QueueElem<T> {
    pub item:T,
    pub priority:usize
}
impl<T> Eq for QueueElem<T> {}
impl<T> Ord for QueueElem<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority.cmp(&self.priority)
    }
}
impl<T> PartialOrd for QueueElem<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.priority.cmp(&self.priority))
    }
}
impl<T> PartialEq<QueueElem<T>> for QueueElem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}


pub struct QueueElemRev<T> {
    pub item:T,
    pub priority:usize
}
impl<T> Eq for QueueElemRev<T> {}
impl<T> Ord for QueueElemRev<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority.cmp(&self.priority)
    }
}
impl<T> PartialOrd for QueueElemRev<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.priority.cmp(&other.priority))
    }
}
impl<T> PartialEq<QueueElemRev<T>> for QueueElemRev<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

