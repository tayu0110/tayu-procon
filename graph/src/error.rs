#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NegativeCycleError;
impl std::fmt::Display for NegativeCycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "This graph has some negative cycles.")
    }
}
impl std::error::Error for NegativeCycleError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CycleDetectionError;
impl std::fmt::Display for CycleDetectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Some Cycles are Detected.")
    }
}
impl std::error::Error for CycleDetectionError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InvalidTree;
impl std::fmt::Display for InvalidTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid Tree")
    }
}
impl std::error::Error for InvalidTree {}
