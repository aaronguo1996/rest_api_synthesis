import React from "react";
import ReactDOM from "react-dom";
import { connect } from "react-redux";
import _ from "underscore";
import * as d3 from "d3";
import { force, graphWidth, graphHeight, scale, drag } from "./forceSimulation"
import { changeChildrenVisibility } from "../../actions";

class CollapsibleGraph extends React.Component {
    
    getVisibleNodes() {
        const {nodes} = this.props;
        const nodeMap = new Map(nodes.map(v => [v.key, v]));
        const getInvisibleChildren = (v) => {
            // hide all the children nodes if the parent is hidden
            // but do not modify the internal states
            if(v.isVisible) {
                return [];
            }

            const invisibleChildren = v.children.map(c => {
                return getInvisibleChildren(nodeMap.get(c));
            });
            return v.children.concat(invisibleChildren.flat());
        }

        const visibleNodes = nodes.filter(v => v.isVisible);
        const invisibleNodes = nodes.filter(v => !v.isVisible);
        const invisibleChildren = invisibleNodes.map(v => 
            getInvisibleChildren(v)).flat();
        const invisibleIndices = invisibleNodes.map(v => v.key)
            .concat(invisibleChildren);
        return visibleNodes.filter(v => !invisibleIndices.includes(v.key));
    }

    getVisibleEdges(nodes) {
        const {links} = this.props;
        const nodeIndices = nodes.map(v => v.key);
        return links.filter(e => nodeIndices.includes(e.source) && 
            nodeIndices.includes(e.target));
    }

    renderChart() {
        const {changeChildrenVisibility} = this.props;
        const old = new Map(this.node.data().map(d => [d.key, d]));
        const visibleNodes = this.getVisibleNodes()
            .map(d => Object.assign(old.get(d.key) || {}, d));
        const visibleLinks = this.getVisibleEdges(visibleNodes)
            .map(d => Object.assign({}, d));

        console.log(visibleNodes);
        
        this.node = this.node
            .data(visibleNodes, d => d.key)
            .join(
                function(enter) {
                    return enter.append("circle");
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .attr("r", 10)
            .attr("fill", d => scale(d.key))
            .call(drag(force))
            .on("click", (_, d) => changeChildrenVisibility({children: d.children}));
        
        this.link = this.link
            .data(visibleLinks, d => [d.source, d.target])
            .join(
                function(enter) {
                    return enter.append("line");
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .attr("stroke-width", 1);

        force.nodes(visibleNodes);
        force.force("link").links(visibleLinks).id(d => d.key)
        // start force calculations after
        // React has taken care of enter/exit of elements
        
        force.on("tick", () => {
            this.link
                .attr("x1", d => d.source.x)
                .attr("y1", d => d.source.y)
                .attr("x2", d => d.target.x)
                .attr("y2", d => d.target.y);

            this.node
                .attr("cx", d => d.x)
                .attr("cy", d => d.y);
        });

        force.alpha(1).restart();
    }

    componentDidMount() {
        this.d3Graph = d3.select(ReactDOM.findDOMNode(this));
        this.link = this.d3Graph.append("g")
            .attr("stroke", "#999")
            .attr("stroke-opacity", 0.6)
            .selectAll("line");
        this.node = this.d3Graph.append("g")
            .attr("stroke", "#fff")
            .attr("stroke-width", 1.5)
            .selectAll("circle");
        this.renderChart();
    }

    componentDidUpdate() {
        this.renderChart();
    }

    render() {
        return (
            <svg width={graphWidth} height={graphHeight}>
            </svg>
        );
    }
};

const mapStateToProps = (state) => {
    return {
        nodes: state.nodes,
        links: state.links,
    };
};

const mapDispatchToProps = (dispatch) => {
    return {
        changeChildrenVisibility: ({ children }) => dispatch(changeChildrenVisibility({ children })),
    };
};

export default connect(mapStateToProps, mapDispatchToProps)(CollapsibleGraph);