<template>
  <div class="chat">
    <div class="header_zone">
      <q-toolbar>
        <q-btn flat round dense class="q-mr-sm">
          <q-avatar size="50px">
            <q-img
              :src="chat.avatar.link"
              class="header_avatar"
              @click="viewFriendProfile(chat.id)"
            />
          </q-avatar>
          <q-tooltip class="bg-accent" :offset="[10, 10]">
            <strong>Ver Perfil</strong>
          </q-tooltip>
        </q-btn>
        <q-toolbar-title class="text-white">{{ chat.nome }}</q-toolbar-title>
        <q-btn
          flat
          round
          dense
          icon="close"
          color="white"
          class="q-mr-sm"
          @click="$emit('closeChat')"
        />
      </q-toolbar>
    </div>
    <q-scroll-area
      class="scroll-zone bg-dark"
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      ref="chatScroll"
    >
      <div class="q-pa-md q-px-lg column bg-dark">
        <q-chat-message
          class="cenas_do_chat text-white"
          v-for="(message, index) in messages"
          :key="index"
          :name="message.id_remetente === chat.id ? chat.nome : 'eu'"
          :avatar="
            message.id_remetente === chat.id ? chat.avatar.link : myavatar
          "
          :text="[message.conteudo]"
          :text-color="message.id_remetente === chat.id ? 'black' : 'white'"
          :sent="message.id_remetente === chat.id ? false : true"
          :bg-color="message.id_remetente === chat.id ? 'secondary' : 'accent'"
        />
      </div>
    </q-scroll-area>
    <div class="bg-black" elevated>
      <q-toolbar>
        <q-form class="full-width" @submit="sendMessage">
          <q-input
            v-model="newMessage"
            bg-color="primary"
            label-color="white"
            input-style="color:white"
            outlined
            rounded
            label="Mensagem"
            dense
            autocomplete="off"
            ref="messageInput"
          >
            <q-btn round dense flat type="submit" color="white" icon="send" />
          </q-input>
        </q-form>
      </q-toolbar>
    </div>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import {
  onBeforeUnmount,
  onMounted,
  onUpdated,
  watch,
} from "@vue/runtime-core";
import { scroll } from "quasar";
const { setVerticalScrollPosition } = scroll;
import axios from "axios";
import URL from "../url.js";
export default {
  props: ["chat", "myavatar"],
  setup(props) {
    const messageInput = ref(null);
    const newMessage = ref("");
    const messages = ref([]);
    var interval = ref("");

    const sendMessage = async () => {
      if (newMessage.value != "") {
        messages.value.push({
          conteudo: newMessage.value,
          id_remetente: localStorage.id,
        });
        const data = newMessage.value;
        newMessage.value = "";

        await axios({
          method: "post",
          url: URL.URL + "/utilizador/addmensagemAmigo/" + localStorage.id,
          params: {
            id_amigo: props.chat.id,
          },
          data: {
            conteudo: data,
          },
        });
      }
      scrollToBottom();
      messageInput.value.focus();
    };

    const chatScroll = ref(null);

    watch(
      () => [...messages.value],
      (val) => {
        if (Object.keys(val).length > messages.value.length) {
          scrollToBottom();
        }
      }
    );

    const scrollToBottom = () => {
      const scrollArea = chatScroll.value;
      const scrollTarget = scrollArea.getScrollTarget();
      setTimeout(() => {
        setVerticalScrollPosition(
          scrollTarget,
          scrollTarget.scrollHeight + 200,
          0
        );
      }, 1);
    };

    onMounted(async () => {
      scrollToBottom();
      const result_msgs = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getMensagensComAmigo/" + localStorage.id,
        params: {
          id_amigo: props.chat.id,
        },
      });
      const result_data_msgs = await result_msgs.data;
      messages.value = result_data_msgs;
      scrollToBottom();
      interval.value = setInterval(async () => {
        const result_msgs = await axios({
          method: "get",
          url: URL.URL + "/utilizador/getMensagensComAmigo/" + localStorage.id,
          params: {
            id_amigo: props.chat.id,
          },
        });
        const result_data_msgs = await result_msgs.data;
        messages.value = result_data_msgs;
      }, 10000);
    });

    onUpdated(async () => {
      const result_msgs = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getMensagensComAmigo/" + localStorage.id,
        params: {
          id_amigo: props.chat.id,
        },
      });
      const result_data_msgs = await result_msgs.data;
      messages.value = result_data_msgs;
      scrollToBottom();
    });

    onBeforeUnmount(() => {
      clearInterval(interval.value);
    });

    return {
      newMessage,
      messages,
      sendMessage,
      chatScroll,
      messageInput,
      thumbStyle: {
        right: "4px",
        borderRadius: "5px",
        backgroundColor: "#ffd208",
        width: "4px",
        opacity: 0.75,
      },
      barStyle: {
        right: "2px",
        borderRadius: "9px",
        width: "2px",
        opacity: 0.2,
      },
    };
  },
  methods: {
    viewFriendProfile(id) {
      this.$emit("closeChat");
      this.$router.push("/friendProfile/" + id);
    },
  },
};
</script>

<style scoped>
.header_zone {
  background: black;
  height: 60px;
  padding-top: 5px;
}
.chat {
  width: 350px;
  left: 75%;
  z-index: 100;
  transition: 0.5s;
}

.scroll-zone {
  height: 400px;
}

.header_avatar {
  width: 50px;
  height: 50px;
}
</style>
