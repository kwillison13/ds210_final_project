use rand::seq::SliceRandom;
use crate::algorithms::most_popular_friend;
use crate::algorithms::shortest_path;
use crate::algorithms::get_random_nodes;
use crate::algorithms::average_path_distance;
type Vertex = usize;
type ListOfEdges = Vec<(Vertex,Vertex)>;
type AdjacencyLists = Vec<Vec<Vertex>>;

mod file_manipulation {
    use std::fs::File;
    use crate::ListOfEdges;
    use std::io::{BufRead, BufReader};

    //reading the file
    pub fn read_file() -> ListOfEdges {
        let file_path = "/Users/keenanwillison/Downloads/Final_project-210/facebook_combined.txt";
        let mut edges = ListOfEdges::new();
        //opening the downloaded file
        match File::open(file_path) {
            Ok(file) => {
                println!("File opened successfully.");
                //going to read the file line by line
                let reader = BufReader::new(file);
                for line in reader.lines() {
                    if let Ok(line_contents) = line {
                        //splitting the data file to put the edges into a list of edges
                        let parts: Vec<usize> = line_contents.split_whitespace().filter_map(|s| s.parse().ok()).collect();
                    if parts.len() >= 2 {
                        edges.push((parts[0], parts[1]));
                    }
                    }
                }
            }
            //will make an error if there's a problem with reading the file
            Err(e) => {
                println!("Failed to open the file: {}", e);
            }
        }
        edges
    }
}

mod graph {
    use crate::AdjacencyLists;
    use crate::ListOfEdges;
    pub struct Graph {
        #[allow(dead_code)]
        pub n: usize, 
        pub outedges: AdjacencyLists,
    }
    
    impl Graph {
        //adding undirected edges to the graph
        fn add_undirected_edges(&mut self, edges:&ListOfEdges) {
            for (u,v) in edges {
                //since my dataset is undirected, we need to push both ways to show they're both connected
                self.outedges[*u].push(*v);
                self.outedges[*v].push(*u);
            }
        }
        //sorts the adjacency list to help it keep the order consistent
        fn sort_graph_lists(&mut self) {
            for edge_list in self.outedges.iter_mut() {
                edge_list.sort();
            }
        }
        //creating an undirected graph based on the given number of vertices and list of edges
        pub fn create_undirected(n:usize,edges:&ListOfEdges) -> Graph {
            let mut new_graph = Graph{n, outedges:vec![vec![];n]};
            new_graph.add_undirected_edges(edges);
            new_graph.sort_graph_lists();
            new_graph                                        
        }
    }
}


mod algorithms {
    use crate::graph::Graph;
    use crate::Vertex;
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use rand::prelude::SliceRandom;
    use rayon::iter::IntoParallelIterator;
    use rayon::iter::ParallelIterator;

    //defining a function called friend_circles to find the different friend circles from the data
    //will be using Breadth-First Search to find the friend circles
    //(the output of friend_circles function relates to connected components)
    pub fn friend_circles(graph: &Graph) -> Vec<Vec<usize>> {
        //setting the visited variable to false to begin because at the start of BFS, all nodes have not been visited yet
        let mut visited = vec![false; graph.n];
        //creating an empty vector of vectors that we will use to store the friend circles at the end of this function
        let mut circles = Vec::new();
        //iterating through each node of the graph
        for node in 0..graph.n {
            if visited[node] == false {
                //creating an empty vector to assign nodes to that belong to a specific friend circle (will reset for every new node visited)
                let mut circle = Vec::new();
                //keeps track of the nodes that need to be visited
                let mut queue: VecDeque<Vertex> = VecDeque::new();
                //if the node has not been visited yet, then it will set it to true once we visit it to make sure we don't visit it again
                visited[node] = true;
                //Queue is used in BFS to keep track of the nodes that need to be explored in further iterations
                //push_back adds the node to back of the queue
                queue.push_back(node);
                //starts a loop as long as there are still nodes in the queue
                while let Some(current_node) = queue.pop_front() {
                    //adds the current node to the circle vector
                    circle.push(current_node);
                    //now we are going to traverse the neighbors of the current node we are on
                    for neighbor in &graph.outedges[current_node] {
                        //checks to see if the neighbor has been visited yet or not
                        if visited[*neighbor] == false {
                            visited[*neighbor] = true;
                            //adds the unvisited neighbor to the back of the queue for further exploration
                            queue.push_back(*neighbor);
                        }
                    }
                }
                //checking to see if the circle vector is empty or not
                //if the circle vector (which we defined above) is not empty, it will push the vector to the circles vector that's defined up top
                //if circle vector is empty, then it won't push anything
                if !circle.is_empty() {
                    //sorting the circle vector so the nodes are shown in order
                    circle.sort();
                    circles.push(circle);
                }
            }
        }
        circles
    }

    //next function is going to look for the "most popular friends"
    //this means I'll be looking for the nodes that lie on the shortest path between other nodes the most frequently
    //(will be finding this based on the betweeness centrality function)
    pub fn most_popular_friend(graph: &Graph, starting_node: usize) -> (HashMap<usize, Vec<Vec<usize>>>, HashMap<usize, usize>) {
        //nodes_visited keeps track of the nodes that our current node has visited while traversing, marking them as true/false
        let mut nodes_visited: Vec<bool> = vec![false; graph.n];
        //paths will store the paths from the node we are on to the other nodes getting traversed
        let mut paths = HashMap::new();
        //will count the number of shortest paths through each node
        let mut number_of_paths = HashMap::new();
        //will be using a queue again for BFS just as we did in the function above
        let mut queue: VecDeque<Vertex> = VecDeque::new();
        //initializing the starting node as true
        nodes_visited[starting_node] = true;
        queue.push_back(starting_node);
        //creating a new HashMap for the current neighbors of the current node we are on
        let mut current_neighbors = HashSet::new();
        //the next_neighbors will store the neighbors in the next layer of the BFS
        let mut next_neighbors = HashSet::new();
        //counting the number of layers traversed by BFS
        let mut layers_traversed = 0;
        current_neighbors.insert(starting_node);
        while !current_neighbors.is_empty() {
            //if the current_neighbors is not empty, then we will add 1 to the layers traversed
            layers_traversed += 1;
            //iterating through each neighbor in current_neighbors
            for &neighbor in &current_neighbors {
                //then it's iterating over the adjacent nodes of the current neighbors using graph.outedges
                for &adjacent_node in &graph.outedges[neighbor] {
                    //checks to see if the adjacent node has been visited or not
                    if nodes_visited[adjacent_node] == false {
                        //if not, it assigns that adjacent node to the next_neighbors set, showing that it belongs to the next BFS layer
                        next_neighbors.insert(adjacent_node);
                        //also pushed it into the queue for further exploration
                        queue.push_back(adjacent_node);
                    }
                }
            }
            for &neighbor in &next_neighbors {
                //setting the neighbor's status to visited = true because we visited it
                nodes_visited[neighbor] = true;
                //then add the neighbor to the queue
                queue.push_back(neighbor);
            }
            //need to clear the values that are in the current_neighbors function in order to move onto the next layer of traversing
            current_neighbors.clear();
            //function to swap the values of two HashMaps
            std::mem::swap(&mut current_neighbors, &mut next_neighbors);
        }
        while let Some(node) = queue.pop_front() {
            //initializes entry for the currenct node we are at, representing the paths from that node to other nodes
            paths.insert(node, Vec::new());
            //initializes the count of paths from the current node
            number_of_paths.insert(node, 1);
            //checking the surrounding neighbors of this node
            for &neighbor in &graph.outedges[node] {
                //checks to see if that neighbor has been visited before
                if nodes_visited[neighbor] {
                    if layers_traversed == 1 {
                        //if the neighbor is the first layer of traversal, the code inserts a new path 
                        paths.entry(node).or_insert_with(Vec::new).push(vec![neighbor]);
                    } else {
                        //if it's not the first layer in traversal, it will retrieve the existing path
                        //or it will create a new vector (path) if that neighbor isn't found
                        let mut neighbor_paths = paths.get(&neighbor).cloned().unwrap_or_else(Vec::new);
                        for path in &mut neighbor_paths {
                            //creating a new path by appending the current node to the start of the path
                            let mut new_path = vec![node];
                            //extends the new path by appending the contents of the existing path
                            new_path.extend_from_slice(path);
                            //pushes the new paths into a vector of paths associated with the node
                            paths.get_mut(&node).unwrap().push(new_path);
                    }
                }
                //gets the number of paths originating from the "neighbor" node and adds 1 to it
                number_of_paths.entry(neighbor).and_modify(|count| *count += 1);
            }
        }
    }
    //returning paths and number of paths
    (paths, number_of_paths)
    }


    //this next function is going to find the shortest path between two "friends" (nodes) from the data set
    pub fn shortest_path(graph: &Graph, node1: Option<usize>, node2: Option<usize>) -> Option<(Vec<usize>, usize, usize)> {
        //checks for valid nodes
        if let (Some(node1), Some(node2)) = (node1, node2) {
            //initializes the BFS by setting up the queue
            let mut queue = VecDeque::new();
            //visited and previous_node set up for tracking and making the paths
            let mut visited = vec![false; graph.n];
            let mut previous_node = vec![None; graph.n];
            //makes node1 visited, and adds it to the queue to start BFS
            visited[node1] = true;
            queue.push_back(node1);
            //performs BFS traversal
            while let Some(current_node) = queue.pop_front() {
                //if current_node == node2, that means our shortest path is found
                if current_node == node2 {
                    //will create a new path
                    let mut path = Vec::new();
                    let mut explored_node = current_node;
                    //constructs the path backwards, by tracing node2 back to node1
                    while let Some(node) = previous_node[explored_node] {
                        path.push(explored_node);
                        explored_node = node;
                    }
                    //once the path is complete, we need to reverse it in order to get the correct path in order from node1 to node2
                    path.push(node1);
                    path.reverse();
                    //if a path is found, it will return the shortest path and both nodes
                    return Some((path, node1, node2));
                }
                //otherwise, if the shortest path is not found, it will explore the neighbors of the current node
                for &neighbor in &graph.outedges[current_node] {
                    if !visited[neighbor] {
                        //if neighbor has been visited, marked true
                        visited[neighbor] = true;
                        //assigns current node as the previous node
                        previous_node[neighbor] = Some(current_node);
                        //adds neighbor to queue
                        queue.push_back(neighbor);
                    }
                }
            }
        }
        //if no path is found, it will return None
        None
    }

    //this function was created to help us get the random nodes for the average_path_distance function (use this function in the main function and tests)
    pub fn get_random_nodes(graph: &Graph, sample_size: usize) -> Vec<usize> {
        let mut rng = rand::thread_rng();
        //creating vector containing the indices of nodes from the graph
        let mut nodes: Vec<usize> = (0..graph.n).collect();
        //shuffling the node indices randomly
        nodes.shuffle(&mut rng);
        //then shortening the vector to the given sample size we want
        nodes.truncate(sample_size);
        nodes
    }

    //this function calculates the average distance between random pairs of nodes in a graph using parallel computation
    pub fn average_path_distance(graph: &Graph, random_nodes: &[usize]) -> f64 {
        //using AtomicUsize to have thread-safe mutable counters (total_path_distance and total_node_pairs)
        let total_path_distance = AtomicUsize::new(0);
        let total_node_pairs = AtomicUsize::new(0);
        //intializes a parallel iteration for the random node pairs (node1 and node2)
        random_nodes.into_par_iter().for_each(|&node1| { 
            for &node2 in random_nodes {
                //checks to see if there's a shortest path between the two random nodes
                if let Some((path, _, _)) = shortest_path(graph, Some(node1), Some(node2)) {
                    //if there is, it gets the length of the path and adds it to total_path_distance
                    total_path_distance.fetch_add(path.len(), Ordering::Relaxed); //Ordering::Relaxed used with atomic operations (like fetch_add)
                    //adds 1 to the total_node pairs if there's a shortest path
                    total_node_pairs.fetch_add(1, Ordering::Relaxed);
                }
            }
        });
        //retrieves total_path_distances and total_nodes_distances as f64 variables
        let total_path_distance = total_path_distance.load(Ordering::Relaxed) as f64;
        let total_node_pairs = total_node_pairs.load(Ordering::Relaxed) as f64;

        //calculates the average path distance (dividing the total path distance by the total node pairs)
        if total_node_pairs > 0.0 {
            total_path_distance / total_node_pairs
        } else {
            0.0
        }
    }
}


#[cfg(test)]
mod tests {
    //importing the Graph struct
    use crate::graph::Graph;
    use crate::ListOfEdges;
    use crate::average_path_distance;
    use crate::get_random_nodes;
    use crate::shortest_path;
    use crate::file_manipulation;
    #[test]
    //testing the shortest_path function
    fn test_shortest_path() {
        //example graph
        let nodes: usize = 5;
        let edges: ListOfEdges = vec![(0,1),(0,2),(1,2),(2,4),(2,3)];
        let graph = Graph::create_undirected(nodes, &edges);
        if let Some((path, node1, node2)) = shortest_path(&graph, Some(0), Some(4)) {
            //checking the individual components of the return statement(the path, node1, and node2)
            //for the shortest path from 0 to 4, should return: [0, 2, 4]
            assert_eq!(path, vec![0, 2, 4]);
            assert_eq!(node1, 0);
            assert_eq!(node2, 4);
        } else {
            panic!("No path found between nodes 0 and 4");
        }
    }
    #[test]
    //testing the average path_distance function
    fn test_average_path_distance() {
        //example graph
        let nodes: usize = 5;
        let edges: ListOfEdges = vec![(0, 1), (0, 2), (1, 2), (2, 4), (2, 3)];
        let graph = Graph::create_undirected(nodes, &edges);
        let sample_size = graph.n;
        let random_nodes = get_random_nodes(&graph, sample_size);
        // Calculating the expected average distance manually
        let mut expected_distance = 0.0;
        let mut node_pairs = 0;
        for &node1 in &random_nodes {
            for &node2 in &random_nodes {
                if let Some((path, _, _)) = shortest_path(&graph, Some(node1), Some(node2)) {
                    //updating the expected_distance
                    expected_distance += path.len() as f64;
                    //adding 1 to node pairs
                    node_pairs += 1;
                }
            }
        }
        //calculating the expectedcaverage distance
        let expected_avg_distance = if node_pairs > 0 {
            expected_distance / node_pairs as f64
        } else {
            0.0
        };
        //comparing the expected average distance with the average distance our function produces
        let avg_distance = average_path_distance(&graph, &random_nodes);
        assert_eq!(avg_distance, expected_avg_distance);
    }
    #[test]
    //testing how many total nodes I have in my dataset
    fn node_count() {
        let edges = file_manipulation::read_file();
        let nodes = edges.iter().map(|&(u, v)| u.max(v)).max().unwrap_or(0) + 1;
        let graph = Graph::create_undirected(nodes, &edges);
        let total_nodes = graph.n;
        assert_eq!(total_nodes, 4039);
    }
    
}

fn main() {
    let edges = file_manipulation::read_file();
    let nodes = edges.iter().map(|&(u, v)| u.max(v)).max().unwrap_or(0) + 1;
    let graph = graph::Graph::create_undirected(nodes, &edges);
    let circles = algorithms::friend_circles(&graph);

    //checking to see if there are friend circles
    if circles.is_empty() {
       println!("No friend circles found");
    } else {
        for (index, circle) in circles.iter().enumerate() {
            //printing the friend circles
            println!("Friend Circle {}: {:?}", index + 1, circle);
            //if the length of the friend circle is equal to the number of nodes in the graph, then we know every friend in the data set is connected
            if circle.len() == graph.n {
                println!("All friends are connected. There are no independent friend groups.")
            } else {
                //if length doesn't equal number of nodes, then we know there are independent friend groups in the data
                println!("There are independent friend groups.");
                //(the output of the friend_circles function is related to connected components, as the friend circles are essentially seeing if the the graph is split up at all)
            }
        }
    }

    //calling the most_popular_friend function to see how many nodes have the most popular friend (node) as part of their shortest paths
    let starting_node = 0;
    let (_paths, num_paths) = most_popular_friend(&graph, starting_node);
    let most_popular_friend = num_paths.iter().max_by_key(|&(_, count)| count);
    if let Some((node, count)) = most_popular_friend {
        println!("The most popular friend is node {} with {} paths", node, count);
    } else {
        println!("No popular friend in the dataset");
    }

    //calling the shortest_path function to get the shortest path between 2 random friends from the dataset
    let random_nodes: Vec<usize> = (0..graph.n).collect();
    let mut rng = rand::thread_rng();
    // Generate two distinct random nodes
    let (random_friend_1, random_friend_2) = (
        *random_nodes.choose(&mut rng).unwrap(), // Get a random node index
        *random_nodes.choose(&mut rng).unwrap(), // Get another random node index
    );
    //if there's a path, it will tell us the nodes you have to go to to get from friend 1 to friend 2
    if let Some((path, node_1, node_2)) = shortest_path(&graph, Some(random_friend_1), Some(random_friend_2)) {
        println!("The shortest path between friend (node) {} and friend (node) {} is: {:?}", node_1, node_2, path);
    } else {
        //if no path, it will tell us no path was found between these two nodes
        println!("There was no path found between friend (node) {} and friend (node) {}.", random_friend_1, random_friend_2)
    }

    //finally, showing the average distance between random pairs of nodes
    //using a random sample size from the data
    let sample_size = 100;
    let random_nodes = get_random_nodes(&graph, sample_size);
    let avg_distance = average_path_distance(&graph, &random_nodes);
    println!("The average distance between {} random pairs of friends (node) is {}.", sample_size, avg_distance);
}