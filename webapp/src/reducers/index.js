import * as Consts from "../constants/action-types"

const initialState = {
    nodes: [
        {
            key: 0,
            name: "user",
            isVisible: true,
            children: [1,2,3],
            parent: null,
            kind: "field",
        },
        {
            key: 1,
            name: "user.id",
            isVisible: true,
            children: [],
            parent: 0,
            kind: "field",
        },
        {
            key: 2,
            name: "user.profile",
            isVisible: true,
            children: [4,5],
            parent: 0,
            kind: "field",
        },
        {
            key: 3,
            name: "user.name",
            isVisible: true,
            children: [],
            parent: 0,
            kind: "field",
        },
        {
            key: 4,
            name: "user.profile.email",
            isVisible: true,
            children: [],
            parent: 2,
            kind: "field",
        },
        {
            key: 5,
            name: "user.profile.photo",
            isVisible: true,
            children: [],
            parent: 2,
            kind: "field",
        },
        {
            key: 6,
            name: "/users.lookupByEmail",
            isVisible: true,
            children: [],
            parent: null,
            kind: "endpoint",
        },
        {
            key: 7,
            name: "/conversations.open",
            isVisible: true,
            children: [],
            parent: null,
            kind: "endpoint",
        },
        {
            key: 8,
            name: "channel.id",
            isVisible: true,
            children: [],
            parent: null,
            kind: "field",
        },
    ],
    links: [
        {
            source: 0,
            target: 1,
        },
        {
            source: 0,
            target: 2,
        },
        {
            source: 0,
            target: 3,
        },
        {
            source: 2,
            target: 4,
        },
        {
            source: 2,
            target: 5,
        },
        {
            source: 0,
            target: 5,
        },
        {
            source: 4,
            target: 6,
        },
        {
            source: 6,
            target: 1,
        },
        {
            source: 1,
            target: 7,
        },
        {
            source: 7,
            target: 8,
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
// const changeVisibilityForEdge = (childrenIndex, e) => {
//     if(childrenIndex.includes(e.source) ||
//         childrenIndex.includes(e.target)) {
//         return {
//             ...e,
//             isVisible: !e.isVisible,
//         };
//     }
//     return e;
// };

const rootReducer = (state = initialState, action) => {
    switch(action.type) {
        case Consts.CHANGE_CHILDREN_VISIBILITY:
            return {
                ...state,
                nodes: state.nodes.map(v => 
                    changeVisibilityForNode(action.payload.children, v)),
                // links: state.links.map(e =>
                //     changeVisibilityForEdge(action.payload.children, e)),
            };
        default:
            return {
                ...state,
            };
    }
}

export default rootReducer;