import * as Consts from "../constants/action-types"

const initialState = {
    nodes: [
        {
            key: 0,
            isVisible: true,
            children: [1,2,3],
        },
        {
            key: 1,
            isVisible: true,
            children: [],
        },
        {
            key: 2,
            isVisible: true,
            children: [4,5],
        },
        {
            key: 3,
            isVisible: true,
            children: [],
        },
        {
            key: 4,
            isVisible: true,
            children: [],
        },
        {
            key: 5,
            isVisible: true,
            children: [],
        },
    ],
    links: [
        {
            source: 0,
            target: 1,
            isVisible: true,
        },
        {
            source: 0,
            target: 2,
            isVisible: true,
        },
        {
            source: 0,
            target: 3,
            isVisible: true,
        },
        {
            source: 2,
            target: 4,
            isVisible: true,
        },
        {
            source: 2,
            target: 5,
            isVisible: true,
        },
    ]
};

// only look at the next level without propagation?
const changeVisibilityForNode = (childrenIndex, v) => {
    if(childrenIndex.includes(v.key)) {
        return {
            ...v,
            isVisible: !v.isVisible,
        };
    }
    return v;
};

// only look at the next level without propagation?
const changeVisibilityForEdge = (childrenIndex, e) => {
    if(childrenIndex.includes(e.source) ||
        childrenIndex.includes(e.target)) {
        return {
            ...e,
            isVisible: !e.isVisible,
        };
    }
    return e;
};

const rootReducer = (state = initialState, action) => {
    switch(action.type) {
        case Consts.CHANGE_CHILDREN_VISIBILITY:
            return {
                ...state,
                nodes: state.nodes.map(v => 
                    changeVisibilityForNode(action.payload.children, v)),
                links: state.links.map(e =>
                    changeVisibilityForEdge(action.payload.children, e)),
            };
        default:
            return {
                ...state,
            };
    }
}

export default rootReducer;