package com.gamehub.Repositories;

import com.gamehub.Model.Users.Mensagem;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.util.Optional;

public interface MensagemRepository extends CrudRepository<Mensagem, Integer> {
    String update_estado_mensagem = "UPDATE mensagem SET lida=True WHERE caixamensagens_id = :caixa_id AND remetente_id != :id_gamer";

    @Modifying
    @Query(value = update_estado_mensagem, nativeQuery = true)
    @Transactional
    void setMensagensLidas(@Param("caixa_id") int caixa_id, @Param("id_gamer") int id_gamer);

    String getNumMensagensByAmigo = "SELECT count(m.id) from gamer as g" +
            " JOIN conversas as c ON c.gamer = g.id" +
            " JOIN mensagem as m ON m.caixamensagens_id = c.caixa_mensagens" +
            " WHERE m.remetente_id != g.id and g.id=:id_gamer and m.lida=False and m.remetente_id=:id_amigo" +
            " group by caixa_mensagens";

    String deleteConversasGamer = "delete from conversas where gamer = :id";

    String deleteConversas = "delete from conversas where caixa_mensagens = :id";

    String deleteCaixasMensagens = "delete from caixa_mensagens where id=:id";

    String deleteMensagensGamer = "delete m.* from mensagem as m" +
            " join caixa_mensagens as cm on m.caixamensagens_id = cm.id" +
            " join conversas as c on c.caixa_mensagens = cm.id" +
            " where c.gamer = :id";
    String deleteMensagensCaixa = "delete from mensagem where caixamensagens_id = :id";

    String deleteMensagensRemetente = "delete from mensagem where remetente_id = :id";


    @Modifying
    @Query(value = deleteConversasGamer, nativeQuery = true)
    @Transactional
    void deleteConversasGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteCaixasMensagens, nativeQuery = true)
    @Transactional
    void deleteCaixasMensagens(@Param("id") int id);

    @Modifying
    @Query(value = deleteMensagensGamer, nativeQuery = true)
    @Transactional
    void deleteMensagensGamer(@Param("id") int id);


    @Query(value = getNumMensagensByAmigo, nativeQuery = true)
    Optional<Integer> getNumMensagensByAmigo(@Param("id_gamer") int id_gamer, @Param("id_amigo") int id_amigo);

    @Modifying
    @Query(value = deleteConversas, nativeQuery = true)
    @Transactional
    void deleteConversas(@Param("id") int id_caixa);

    @Modifying
    @Query(value = deleteMensagensCaixa, nativeQuery = true)
    @Transactional
    void deleteMensagensCaixa(@Param("id")int id_caixa);

    @Modifying
    @Query(value = deleteMensagensRemetente, nativeQuery = true)
    @Transactional
    void deleteMensagensRemetente(@Param("id")int id);
}
